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
	"time"

	"github.com/gin-gonic/gin"
)

func validStorageTestCertificate() CertV1 {
	return CertV1{
		BundleID:     "bundle",
		PolicyHash:   "policy",
		ProofHash:    "proof",
		AutomataHash: "automata",
		LabelerHash:  "labeler",
		NIClaim:      "test",
		NIMonitor:    "inapplicable",
		SidecarBuild: "test",
		TenantID:     "tenant-1",
		SessionID:    "session-1",
		Timestamp:    time.Unix(1740000000, 0).UTC(),
	}
}

func TestEvidenceStorageAcceptsValidIdentifiers(t *testing.T) {
	storage := filepath.Join(t.TempDir(), "evidence")
	service := &EvidenceService{storagePath: storage}
	cert := validStorageTestCertificate()

	if err := service.StoreCertificate(context.Background(), cert); err != nil {
		t.Fatalf("store valid certificate: %v", err)
	}

	path := filepath.Join(storage, "certs", cert.TenantID, cert.SessionID)
	entries, err := os.ReadDir(path)
	if err != nil {
		t.Fatalf("read certificate directory: %v", err)
	}
	if len(entries) != 1 || !strings.HasSuffix(entries[0].Name(), ".cert.json") {
		t.Fatalf("unexpected certificate files: %v", entries)
	}

	data, err := os.ReadFile(filepath.Join(path, entries[0].Name()))
	if err != nil {
		t.Fatalf("read certificate: %v", err)
	}
	var got CertV1
	if err := json.Unmarshal(data, &got); err != nil {
		t.Fatalf("decode certificate: %v", err)
	}
	if got.TenantID != cert.TenantID || got.SessionID != cert.SessionID {
		t.Fatalf("certificate identity changed: %+v", got)
	}
}

func TestEvidenceStorageRejectsUnsafeIdentifiersBeforeSideEffects(t *testing.T) {
	cases := []struct {
		name   string
		value  string
		tenant bool
	}{
		{"empty", "", true},
		{"dot", ".", true},
		{"dot-dot", "..", true},
		{"parent-traversal", "../outside", true},
		{"nested", "tenant/other", true},
		{"absolute-style", "/tmp/outside", true},
		{"backslash", "tenant\\other", true},
		{"colon", "tenant:other", true},
		{"nul", "tenant\x00other", true},
		{"too-long", strings.Repeat("t", 256), true},
		{"session-parent-traversal", "../outside", false},
		{"session-absolute-style", "/tmp/outside", false},
		{"session-backslash", "session\\other", false},
		{"session-empty", "", false},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			storage := filepath.Join(t.TempDir(), "evidence")
			service := &EvidenceService{storagePath: storage}
			cert := validStorageTestCertificate()
			if tc.tenant {
				cert.TenantID = tc.value
			} else {
				cert.SessionID = tc.value
			}
			if err := service.StoreCertificate(context.Background(), cert); err == nil {
				t.Fatalf("accepted unsafe identifier %q", tc.value)
			}
			if _, err := os.Stat(storage); !os.IsNotExist(err) {
				t.Fatalf("rejected certificate modified storage: %v", err)
			}
			if err := service.storeCertInFS(cert); err == nil {
				t.Fatalf("filesystem boundary accepted unsafe identifier %q", tc.value)
			}
		})
	}
}

func TestEvidenceStorageRejectsSymlinkOutsideRoot(t *testing.T) {
	base := t.TempDir()
	storage := filepath.Join(base, "evidence")
	outside := filepath.Join(base, "outside")
	if err := os.MkdirAll(filepath.Join(storage, "certs"), 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(outside, 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outside, filepath.Join(storage, "certs", "tenant-1")); err != nil {
		t.Skipf("symlink creation unavailable: %v", err)
	}

	service := &EvidenceService{storagePath: storage}
	if err := service.storeCertInFS(validStorageTestCertificate()); err == nil {
		t.Fatal("certificate escaped through a tenant symlink")
	}
	entries, err := os.ReadDir(outside)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("certificate written outside storage root: %v", entries)
	}
}

func TestEvidenceStoreHTTPRejectsTraversal(t *testing.T) {
	gin.SetMode(gin.TestMode)
	storage := filepath.Join(t.TempDir(), "evidence")
	service := &EvidenceService{storagePath: storage}
	cert := validStorageTestCertificate()
	cert.TenantID = "../outside"

	payload, err := json.Marshal(cert)
	if err != nil {
		t.Fatal(err)
	}
	router := gin.New()
	router.POST("/api/v1/evidence/cert", service.storeCertHandler)
	request := httptest.NewRequest(http.MethodPost, "/api/v1/evidence/cert", bytes.NewReader(payload))
	request.Header.Set("Content-Type", "application/json")
	recorder := httptest.NewRecorder()
	router.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusBadRequest {
		t.Fatalf("HTTP %d, expected 400: %s", recorder.Code, recorder.Body.String())
	}
	var response struct {
		Error struct {
			Code string `json:"code"`
		} `json:"error"`
	}
	if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
		t.Fatalf("decode response: %v", err)
	}
	if response.Error.Code != "INVALID_CERTIFICATE" {
		t.Fatalf("unexpected response: %s", recorder.Body.String())
	}
	if _, err := os.Stat(storage); !os.IsNotExist(err) {
		t.Fatalf("HTTP rejection modified storage: %v", err)
	}
}
