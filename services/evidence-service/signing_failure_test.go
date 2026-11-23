// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// controlledSigner exercises failure modes independently of a key provider.
type controlledSigner struct {
	signature string
	err       error
}

func (s controlledSigner) Sign([]byte) (string, error) {
	return s.signature, s.err
}

func TestEvidenceSigningFailureLeavesNoFilesystemRecord(t *testing.T) {
	tests := []struct {
		name   string
		signer Signer
	}{
		{"provider_failure", controlledSigner{err: errors.New("signer offline")}},
		{"empty_signature", controlledSigner{}},
		{"invalid_encoding", controlledSigner{signature: "not-base64!"}},
		{"wrong_signature_length", controlledSigner{signature: base64.RawURLEncoding.EncodeToString([]byte("short"))}},
		{"unimplemented_kms", &kmsSigner{}},
		{"unimplemented_vault", &vaultSigner{}},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			storage := filepath.Join(t.TempDir(), "evidence")
			service := &EvidenceService{storagePath: storage, signer: tc.signer}
			if err := service.StoreCertificate(context.Background(), validStorageTestCertificate()); err == nil {
				t.Fatal("a signing failure was reported as successful issuance")
			}
			if _, err := os.Stat(storage); !os.IsNotExist(err) {
				t.Fatalf("failed issuance created filesystem state: %v", err)
			}
		})
	}
}

func TestEvidenceSignatureCoversPersistedPermissionFields(t *testing.T) {
	public, private, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatalf("generate disposable signing key: %v", err)
	}
	storage := filepath.Join(t.TempDir(), "evidence")
	service := &EvidenceService{storagePath: storage, signer: &fileSigner{priv: private}}
	cert := validStorageTestCertificate()
	cert.Sig = "caller-provided-untrusted-signature"
	cert.Extensions = map[string]interface{}{"source": "fixture"}
	cert.PermitDecision = "permit"
	cert.PathWitnessOK = true
	cert.LabelDerivationOK = true
	cert.Epoch = 7

	if err := service.StoreCertificate(context.Background(), cert); err != nil {
		t.Fatalf("store signed certificate: %v", err)
	}
	if _, exists := cert.Extensions["path_witness_ok"]; exists {
		t.Fatal("issuance mutated caller-owned certificate extensions")
	}
	folder := filepath.Join(storage, "certs", cert.TenantID, cert.SessionID)
	files, err := os.ReadDir(folder)
	if err != nil {
		t.Fatalf("read signed certificate directory: %v", err)
	}
	if len(files) != 1 {
		t.Fatalf("expected exactly one certificate file, got %d", len(files))
	}
	data, err := os.ReadFile(filepath.Join(folder, files[0].Name()))
	if err != nil {
		t.Fatalf("read signed certificate: %v", err)
	}
	var stored CertV1
	if err := json.Unmarshal(data, &stored); err != nil {
		t.Fatalf("decode stored certificate: %v", err)
	}
	if stored.Sig == cert.Sig || stored.Sig == "" {
		t.Fatal("storage retained caller signature or omitted service signature")
	}
	if stored.Extensions["permit_decision"] != "permit" ||
		stored.Extensions["path_witness_ok"] != true ||
		stored.Extensions["label_derivation_ok"] != true ||
		stored.Extensions["permission_epoch"] != float64(7) {
		t.Fatalf("signed certificate omitted permission evidence: %+v", stored.Extensions)
	}

	signature, err := base64.RawURLEncoding.DecodeString(stored.Sig)
	if err != nil {
		t.Fatalf("decode stored signature: %v", err)
	}
	stored.Sig = ""
	unsigned, err := json.Marshal(stored)
	if err != nil {
		t.Fatalf("encode unsigned certificate: %v", err)
	}
	var fields map[string]interface{}
	if err := json.Unmarshal(unsigned, &fields); err != nil {
		t.Fatalf("parse unsigned claims: %v", err)
	}
	canonical, err := marshalCanonicalJSON(fields)
	if err != nil {
		t.Fatalf("canonicalize persisted certificate: %v", err)
	}
	if !ed25519.Verify(public, canonical, signature) {
		t.Fatal("persisted certificate fields do not verify against issuance key")
	}
	fields["tenant_id"] = "other-tenant"
	tampered, err := marshalCanonicalJSON(fields)
	if err != nil {
		t.Fatalf("canonicalize tampered certificate: %v", err)
	}
	if ed25519.Verify(public, tampered, signature) {
		t.Fatal("signature accepted modified tenant identity")
	}
}

func TestEvidenceRejectsUnverifiedCallerSignature(t *testing.T) {
	storage := filepath.Join(t.TempDir(), "evidence")
	service := &EvidenceService{storagePath: storage}
	cert := validStorageTestCertificate()
	cert.Sig = "untrusted-signature"

	if err := service.StoreCertificate(context.Background(), cert); err == nil {
		t.Fatal("unsigned service accepted a caller-supplied signature")
	}
	if _, err := os.Stat(storage); !os.IsNotExist(err) {
		t.Fatalf("rejected caller signature created storage: %v", err)
	}
}

func TestUnavailableSignerBackendsAreRejectedAtConfiguration(t *testing.T) {
	for _, backend := range []string{"kms", "vault", "file"} {
		t.Run(backend, func(t *testing.T) {
			t.Setenv("CERT_SIGNER_BACKEND", backend)
			t.Setenv("CERT_SIGNER_FILE", "")
			if _, err := newSignerFromEnv(); err == nil {
				t.Fatalf("backend %s was accepted without a signing implementation", backend)
			}
		})
	}
}

func TestEvidenceInvalidCanonicalPayloadFailsBeforeStorage(t *testing.T) {
	storage := filepath.Join(t.TempDir(), "evidence")
	service := &EvidenceService{storagePath: storage, signer: controlledSigner{signature: strings.Repeat("A", 86)}}
	cert := validStorageTestCertificate()
	cert.Extensions = map[string]interface{}{"unsupported": make(chan int)}
	if err := service.StoreCertificate(context.Background(), cert); err == nil {
		t.Fatal("invalid signing payload was persisted")
	}
	if _, err := os.Stat(storage); !os.IsNotExist(err) {
		t.Fatalf("invalid signing payload created storage: %v", err)
	}
}
