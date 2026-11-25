// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"database/sql"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
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
	testEvidenceHTTPAccess(t, nil, nil)
}

func TestEvidencePostgresHTTPAccessBindsTenantAndPermission(t *testing.T) {
	admin := openDisposablePostgres(t)
	if err := (&EvidenceService{db: admin}).initializeSchema(); err != nil {
		t.Fatal(err)
	}
	role := "evidence_http_" + strings.ReplaceAll(uuid.NewString(), "-", "")
	password := uuid.NewString()
	if _, err := admin.Exec("CREATE ROLE " + role + " LOGIN NOSUPERUSER NOBYPASSRLS PASSWORD '" + password + "'"); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if _, err := admin.Exec("DROP OWNED BY " + role + "; DROP ROLE " + role); err != nil {
			t.Errorf("remove restricted fixture role: %v", err)
		}
	})
	if _, err := admin.Exec("GRANT USAGE ON SCHEMA public TO " + role + "; GRANT SELECT, INSERT ON certificates TO " + role); err != nil {
		t.Fatal(err)
	}
	dsn, err := url.Parse(os.Getenv("EVIDENCE_TEST_DATABASE_URL"))
	if err != nil {
		t.Fatal(err)
	}
	dsn.User = url.UserPassword(role, password)
	db, err := sql.Open("postgres", dsn.String())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = db.Close() })
	db.SetMaxOpenConns(1)
	db.SetMaxIdleConns(1)
	if err := db.Ping(); err != nil {
		t.Fatal(err)
	}
	var bypass bool
	if err := db.QueryRow("SELECT rolsuper OR rolbypassrls FROM pg_roles WHERE rolname = current_user").Scan(&bypass); err != nil || bypass {
		t.Fatalf("restricted role has unexpected privileges: %v", err)
	}
	testEvidenceHTTPAccess(t, db, admin)
}

func testEvidenceHTTPAccess(t *testing.T, db, admin *sql.DB) {
	t.Helper()
	gin.SetMode(gin.TestMode)
	tenantA, tenantB := "access-a-"+uuid.NewString(), "access-b-"+uuid.NewString()
	a, tokenA := evidenceTestCredential(t, tenantA, true, true)
	b, tokenB := evidenceTestCredential(t, tenantB, true, true)
	reader, readToken := evidenceTestCredential(t, tenantA, true, false)
	writer, writeToken := evidenceTestCredential(t, tenantA, false, true)
	_, unknownToken := evidenceTestCredential(t, tenantA, true, true)
	service := &EvidenceService{db: db, storagePath: t.TempDir(), access: []evidenceCredential{a, b, reader, writer}}
	if db != nil {
		t.Cleanup(func() {
			if _, err := admin.Exec("DELETE FROM certificates WHERE tenant_id IN ($1, $2)", tenantA, tenantB); err != nil {
				t.Errorf("remove disposable HTTP isolation records: %v", err)
			}
		})
	}
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
	call("POST", "/cert", "", cert(tenantA), 401)
	call("POST", "/cert", unknownToken, cert(tenantA), 401)
	call("POST", "/cert", readToken, cert(tenantA), 403)
	call("POST", "/cert", tokenA, cert(tenantB), 403)
	call("POST", "/cert", tokenA, cert(tenantA), 201)
	call("POST", "/cert", tokenB, cert(tenantB), 201)

	call("POST", "/search", "", empty, 401)
	call("POST", "/search", writeToken, empty, 403)
	call("POST", "/search", readToken, map[string]string{"tenant_id": tenantB}, 403)
	for tenant, token := range map[string]string{tenantA: tokenA, tenantB: tokenB} {
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
	call("POST", "/packet", tokenA, map[string]string{"tenant_id": tenantB}, 403)
	var packet CompliancePacket
	if err := json.Unmarshal(call("POST", "/packet", readToken, empty, 200), &packet); err != nil ||
		packet.TenantID != tenantA || len(packet.Certificates) != 1 || packet.Certificates[0].TenantID != tenantA {
		t.Fatalf("packet did not preserve tenant scope: %v", err)
	}
	if !strings.Contains(packet.Conformance, "Policy \"policy\"") ||
		!strings.Contains(packet.Conformance, "Recorded accept rate:") ||
		strings.Contains(packet.Conformance, "Compliance Rate:") {
		t.Fatal("diagnostic misrepresents or truncates recorded assertions")
	}
	if db != nil {
		// Both tenants' rows exist in the real database. Introduce a
		// deliberately inconsistent stored record and require a failed query.
		var count int
		if err := db.QueryRow("SELECT COUNT(*) FROM certificates").Scan(&count); err != nil || count != 0 {
			t.Fatalf("tenant escaped transaction into pooled connection: count=%d err=%v", count, err)
		}
		if _, err := admin.Exec("UPDATE certificates SET cert_data = jsonb_set(cert_data, '{tenant_id}', to_jsonb($1::text)) WHERE tenant_id = $2", tenantB, tenantA); err != nil {
			t.Fatal(err)
		}
		call("POST", "/search", tokenA, empty, 500)
		call("GET", "/cert/shared-session", tokenA, nil, 500)
		call("POST", "/packet", tokenA, empty, 500)
	}
	service.signer = controlledSigner{}
	call("POST", "/cert", tokenA, cert(tenantA), 503)
	service.access = nil
	call("POST", "/search", tokenA, empty, 503)
}
