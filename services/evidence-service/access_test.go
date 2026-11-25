// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

func evidenceTestCredential(t *testing.T, tenant string, read, write bool) (evidenceCredential, string) {
	t.Helper()
	var raw [32]byte
	if _, err := rand.Read(raw[:]); err != nil {
		t.Fatal(err)
	}
	return evidenceCredential{tenant: tenant, digest: sha256.Sum256(raw[:]), read: read, write: write},
		"Bearer " + base64.RawURLEncoding.EncodeToString(raw[:])
}

func TestEvidenceAccessConfiguration(t *testing.T) {
	credential, _ := evidenceTestCredential(t, "tenant-a", true, false)
	entry := evidenceAccessEntry{Tenant: credential.tenant, TokenSHA256: hex.EncodeToString(credential.digest[:]), Read: true}
	path := filepath.Join(t.TempDir(), "access.json")
	valid, err := json.Marshal([]evidenceAccessEntry{entry})
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, valid, 0600); err != nil {
		t.Fatal(err)
	}
	got, err := loadEvidenceAccess(path)
	if err != nil || len(got) != 1 || got[0] != credential {
		t.Fatalf("valid configuration rejected: %v", err)
	}
	duplicate, err := json.Marshal([]evidenceAccessEntry{entry, entry})
	if err != nil {
		t.Fatal(err)
	}
	for _, invalid := range []string{"[]", "null", string(duplicate), string(valid) + " true",
		strings.Replace(string(valid), "tenant-a", "../outside", 1),
		strings.Replace(string(valid), entry.TokenSHA256, "bad", 1),
		strings.Replace(string(valid), `"read":true`, `"read":false`, 1),
		strings.Replace(string(valid), `"read":true`, `"unknown":true`, 1)} {
		if err := os.WriteFile(path, []byte(invalid), 0600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadEvidenceAccess(path); err == nil {
			t.Fatal("invalid credential configuration accepted")
		}
	}
	if keys, err := loadEvidenceAccess(""); err != nil || len(keys) != 0 {
		t.Fatalf("unconfigured access is not unavailable: %v", err)
	}
}

func TestEvidenceHTTPAccessBindsTenantAndPermission(t *testing.T) {
	gin.SetMode(gin.TestMode)
	a, tokenA := evidenceTestCredential(t, "tenant-a", true, true)
	b, tokenB := evidenceTestCredential(t, "tenant-b", true, true)
	reader, readToken := evidenceTestCredential(t, "tenant-a", true, false)
	writer, writeToken := evidenceTestCredential(t, "tenant-a", false, true)
	_, unknownToken := evidenceTestCredential(t, "tenant-a", true, true)
	service := &EvidenceService{storagePath: t.TempDir(), access: []evidenceCredential{a, b, reader, writer}}
	router := gin.New()
	router.POST("/cert", service.storeCertHandler)
	router.POST("/search", service.searchCertsHandler)
	router.GET("/cert/:id", service.getCertHandler)
	router.POST("/packet", service.buildPacketHandler)

	call := func(method, path, token string, body interface{}, expected int) []byte {
		t.Helper()
		var data []byte
		if body != nil {
			var err error
			data, err = json.Marshal(body)
			if err != nil {
				t.Fatal(err)
			}
		}
		req := httptest.NewRequest(method, path, bytes.NewReader(data))
		req.Header.Set("Content-Type", "application/json")
		if token != "" {
			req.Header.Set("Authorization", token)
		}
		rec := httptest.NewRecorder()
		router.ServeHTTP(rec, req)
		if rec.Code != expected {
			t.Fatalf("%s %s: HTTP %d, expected %d: %s", method, path, rec.Code, expected, rec.Body.String())
		}
		return rec.Body.Bytes()
	}
	cert := func(tenant string) map[string]interface{} {
		return map[string]interface{}{
			"bundle_id": "bundle", "policy_hash": "policy", "proof_hash": "proof",
			"automata_hash": "automata", "labeler_hash": "labeler", "ni_claim": "fixture",
			"ni_monitor": "inapplicable", "sidecar_build": "fixture",
			"tenant_id": tenant, "session_id": "shared-session", "timestamp": "2026-01-01T00:00:00Z",
		}
	}
	empty := map[string]interface{}{}
	call("POST", "/cert", "", cert("tenant-a"), 401)
	call("POST", "/cert", unknownToken, cert("tenant-a"), 401)
	call("POST", "/cert", readToken, cert("tenant-a"), 403)
	call("POST", "/cert", tokenA, cert("tenant-b"), 403)
	call("POST", "/cert", tokenA, cert("tenant-a"), 201)
	call("POST", "/cert", tokenB, cert("tenant-b"), 201)

	call("POST", "/search", "", empty, 401)
	call("POST", "/search", writeToken, empty, 403)
	call("POST", "/search", readToken, map[string]string{"tenant_id": "tenant-b"}, 403)
	for tenant, token := range map[string]string{"tenant-a": tokenA, "tenant-b": tokenB} {
		var response CertSearchResponse
		if err := json.Unmarshal(call("POST", "/search", token, empty, 200), &response); err != nil {
			t.Fatal(err)
		}
		if response.Total != 1 || len(response.Certificates) != 1 || response.Certificates[0].TenantID != tenant {
			t.Fatalf("search did not preserve tenant scope: %+v", response)
		}
		var record CertV1
		if err := json.Unmarshal(call("GET", "/cert/shared-session", token, nil, 200), &record); err != nil || record.TenantID != tenant {
			t.Fatalf("session lookup crossed tenant scope: %v", err)
		}
	}
	call("GET", "/cert/shared-session", "", nil, 401)
	call("POST", "/packet", tokenA, map[string]string{"tenant_id": "tenant-b"}, 403)
	var packet CompliancePacket
	if err := json.Unmarshal(call("POST", "/packet", readToken, empty, 200), &packet); err != nil ||
		packet.TenantID != "tenant-a" || len(packet.Certificates) != 1 || packet.Certificates[0].TenantID != "tenant-a" {
		t.Fatalf("packet did not preserve tenant scope: %v", err)
	}
	service.signer = controlledSigner{}
	call("POST", "/cert", tokenA, cert("tenant-a"), 503)
	service.access = nil
	call("POST", "/search", tokenA, empty, 503)
}
