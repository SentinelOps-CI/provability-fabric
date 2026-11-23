// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

func TestEvidenceSearchRejectsNegativePagination(t *testing.T) {
	service := &EvidenceService{storagePath: filepath.Join(t.TempDir(), "evidence")}
	for _, req := range []CertSearchRequest{
		{Limit: 10, Offset: -1},
		{Limit: -1},
		{Limit: -1, Offset: -1},
	} {
		if result, err := service.SearchCertificates(context.Background(), req); err == nil || result != nil {
			t.Fatalf("invalid pagination %+v returned result=%+v, err=%v", req, result, err)
		}
	}
}

func TestEvidenceSearchHTTPRejectsNegativePagination(t *testing.T) {
	gin.SetMode(gin.TestMode)
	service := &EvidenceService{storagePath: filepath.Join(t.TempDir(), "evidence")}
	router := gin.New()
	router.POST("/api/v1/evidence/search", service.searchCertsHandler)
	for _, payload := range []string{
		`{"offset":-1,"limit":10}`,
		`{"offset":0,"limit":-1}`,
	} {
		t.Run(payload, func(t *testing.T) {
			request := httptest.NewRequest(http.MethodPost, "/api/v1/evidence/search", bytes.NewBufferString(payload))
			request.Header.Set("Content-Type", "application/json")
			recorder := httptest.NewRecorder()
			router.ServeHTTP(recorder, request)
			if recorder.Code != http.StatusBadRequest {
				t.Fatalf("invalid pagination returned HTTP %d: %s", recorder.Code, recorder.Body.String())
			}
			var response struct {
				Error struct {
					Code string `json:"code"`
				} `json:"error"`
			}
			if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
				t.Fatalf("decode rejection: %v", err)
			}
			if response.Error.Code != "INVALID_REQUEST" {
				t.Fatalf("unexpected error code %q", response.Error.Code)
			}
		})
	}
}

func TestEvidenceSearchEmptyStoreAndExtremeOffset(t *testing.T) {
	service := &EvidenceService{storagePath: filepath.Join(t.TempDir(), "evidence")}
	empty, err := service.SearchCertificates(context.Background(), CertSearchRequest{})
	if err != nil || empty.Total != 0 || len(empty.Certificates) != 0 {
		t.Fatalf("new evidence store must be empty: result=%+v err=%v", empty, err)
	}
	if err := service.StoreCertificate(context.Background(), validStorageTestCertificate()); err != nil {
		t.Fatalf("store valid fixture: %v", err)
	}
	result, err := service.SearchCertificates(context.Background(), CertSearchRequest{
		Limit: 1000, Offset: int(^uint(0) >> 1),
	})
	if err != nil || result.Total != 1 || len(result.Certificates) != 0 {
		t.Fatalf("extreme offset must return an empty page: result=%+v err=%v", result, err)
	}
}

func TestEvidenceSearchRejectsMalformedFilesystemCertificate(t *testing.T) {
	service := &EvidenceService{storagePath: filepath.Join(t.TempDir(), "evidence")}
	cert := validStorageTestCertificate()
	if err := service.StoreCertificate(context.Background(), cert); err != nil {
		t.Fatal(err)
	}
	folder := filepath.Join(service.storagePath, "certs", cert.TenantID, cert.SessionID)
	if err := os.WriteFile(filepath.Join(folder, "malformed.cert.json"), []byte("{not-json"), 0600); err != nil {
		t.Fatal(err)
	}
	result, err := service.SearchCertificates(context.Background(), CertSearchRequest{TenantID: cert.TenantID})
	if err == nil || result != nil || !strings.Contains(err.Error(), "decode filesystem certificate") {
		t.Fatalf("corrupted certificate was omitted from successful search: result=%+v err=%v", result, err)
	}
}

func TestEvidenceSearchRejectsCertificateSymlink(t *testing.T) {
	storage := filepath.Join(t.TempDir(), "evidence")
	folder := filepath.Join(storage, "certs", "tenant-1")
	if err := os.MkdirAll(folder, 0700); err != nil {
		t.Fatal(err)
	}
	outside := filepath.Join(t.TempDir(), "outside.cert.json")
	payload, err := json.Marshal(validStorageTestCertificate())
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(outside, payload, 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outside, filepath.Join(folder, "linked.cert.json")); err != nil {
		t.Skipf("symlink creation unavailable: %v", err)
	}
	service := &EvidenceService{storagePath: storage}
	result, err := service.SearchCertificates(context.Background(), CertSearchRequest{})
	if err == nil || result != nil || !strings.Contains(err.Error(), "symlink in certificate storage") {
		t.Fatalf("certificate symlink was followed or ignored: result=%+v err=%v", result, err)
	}
}

func TestEvidencePostgresSearchRejectsMalformedCertificateRow(t *testing.T) {
	db := openDisposablePostgres(t)
	service := &EvidenceService{db: db}
	if err := service.initializeSchema(); err != nil {
		t.Fatalf("initialize disposable database: %v", err)
	}
	tenant := "invalid-json-" + uuid.NewString()
	cert := validStorageTestCertificate()
	cert.TenantID = tenant
	_, err := db.Exec(`
		INSERT INTO certificates (
			bundle_id, policy_hash, proof_hash, automata_hash, labeler_hash,
			ni_claim, ni_monitor, sidecar_build, tenant_id, session_id,
			timestamp, cert_data
		) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12)
	`, cert.BundleID, cert.PolicyHash, cert.ProofHash,
		cert.AutomataHash, cert.LabelerHash, cert.NIClaim, cert.NIMonitor,
		cert.SidecarBuild, tenant, cert.SessionID, cert.Timestamp, "[]")
	if err != nil {
		t.Fatalf("insert malformed disposable certificate record: %v", err)
	}
	t.Cleanup(func() {
		if _, err := db.Exec("DELETE FROM certificates WHERE tenant_id = $1", tenant); err != nil {
			t.Errorf("clean up malformed row fixture: %v", err)
		}
	})
	result, err := service.SearchCertificates(context.Background(), CertSearchRequest{TenantID: tenant})
	if err == nil || result != nil || !strings.Contains(err.Error(), "decode stored certificate row") {
		t.Fatalf("database search omitted malformed row: result=%+v err=%v", result, err)
	}
}
