// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package dsse

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func fixtureDir(t *testing.T) string {
	t.Helper()
	for _, base := range []string{
		filepath.Join("..", "..", "..", "tests", "fixtures", "crypto"),
		filepath.Join("tests", "fixtures", "crypto"),
	} {
		if _, err := os.Stat(filepath.Join(base, "ed25519_public.pem")); err == nil {
			return base
		}
	}
	t.Skip("crypto fixtures not found")
	return ""
}

func TestVerifyFixtureEnvelope(t *testing.T) {
	base := fixtureDir(t)
	pemPath := filepath.Join(base, "ed25519_public.pem")
	envPath := filepath.Join(base, "dsse_sample_envelope.json")

	t.Setenv(EnvTrustRootPEM, pemPath)
	t.Setenv(EnvEnforceDSSE, "1")

	envB, err := os.ReadFile(envPath)
	if err != nil {
		t.Fatalf("read envelope: %v", err)
	}
	env, err := ParseEnvelopeJSON(envB)
	if err != nil {
		t.Fatalf("parse envelope: %v", err)
	}
	result := VerifyEnvelope(env, AccessReceiptType)
	if !result.Valid {
		t.Fatalf("expected valid envelope, got %s", result.Reason)
	}
}

func TestEnforceDSSEDefaultAndOptOut(t *testing.T) {
	t.Setenv(EnvEnforceDSSE, "")
	if !EnforceDSSE() {
		t.Fatal("empty/unset PF_ENFORCE_DSSE must enforce (fail-closed default)")
	}

	t.Setenv(EnvEnforceDSSE, "1")
	if !EnforceDSSE() {
		t.Fatal("PF_ENFORCE_DSSE=1 must enforce")
	}
	t.Setenv(EnvEnforceDSSE, "true")
	if !EnforceDSSE() {
		t.Fatal("PF_ENFORCE_DSSE=true must enforce")
	}

	t.Setenv(EnvEnforceDSSE, "0")
	if EnforceDSSE() {
		t.Fatal("PF_ENFORCE_DSSE=0 must opt out")
	}
	t.Setenv(EnvEnforceDSSE, "false")
	if EnforceDSSE() {
		t.Fatal("PF_ENFORCE_DSSE=false must opt out")
	}
}

func TestRejectUnsignedWhenUnset(t *testing.T) {
	t.Setenv(EnvEnforceDSSE, "")
	t.Setenv(EnvTrustRootPEM, "")
	err := VerifyAccessReceipt(AccessReceiptPayload{
		ReceiptID:  "rcpt-1",
		Tenant:     "tenant-a",
		IndexShard: "shard-0",
	}, "ed25519", "deadbeef")
	if err == nil {
		t.Fatal("expected reject when enforcing without trust root")
	}
	if !strings.Contains(err.Error(), "trust root") {
		t.Fatalf("expected trust root error, got: %v", err)
	}
}

func TestStructuralPassWhenOptOut(t *testing.T) {
	t.Setenv(EnvEnforceDSSE, "0")
	t.Setenv(EnvTrustRootPEM, "")
	err := VerifyAccessReceipt(AccessReceiptPayload{
		ReceiptID:  "rcpt-1",
		Tenant:     "tenant-a",
		IndexShard: "shard-0",
	}, "ed25519", "deadbeef")
	if err != nil {
		t.Fatalf("opt-out should skip crypto: %v", err)
	}
}

func TestRejectTamperedPayload(t *testing.T) {
	base := fixtureDir(t)
	pemPath := filepath.Join(base, "ed25519_public.pem")
	envPath := filepath.Join(base, "dsse_sample_envelope.json")

	t.Setenv(EnvTrustRootPEM, pemPath)

	envB, err := os.ReadFile(envPath)
	if err != nil {
		t.Fatalf("read envelope: %v", err)
	}
	var env Envelope
	if err := json.Unmarshal(envB, &env); err != nil {
		t.Fatalf("parse: %v", err)
	}
	env.Payload = env.Payload[:len(env.Payload)-2] + "XX"
	result := VerifyEnvelope(env, AccessReceiptType)
	if result.Valid {
		t.Fatal("expected tampered payload to be rejected")
	}
}

func TestRejectTamperedSignature(t *testing.T) {
	base := fixtureDir(t)
	pemPath := filepath.Join(base, "ed25519_public.pem")
	envPath := filepath.Join(base, "dsse_sample_envelope.json")

	t.Setenv(EnvTrustRootPEM, pemPath)

	envB, err := os.ReadFile(envPath)
	if err != nil {
		t.Fatalf("read envelope: %v", err)
	}
	var env Envelope
	if err := json.Unmarshal(envB, &env); err != nil {
		t.Fatalf("parse: %v", err)
	}
	if len(env.Signatures) == 0 {
		t.Fatal("no signatures")
	}
	env.Signatures[0].Sig = env.Signatures[0].Sig[:len(env.Signatures[0].Sig)-4] + "AAAA"
	result := VerifyEnvelope(env, AccessReceiptType)
	if result.Valid {
		t.Fatal("expected tampered signature to be rejected")
	}
}
