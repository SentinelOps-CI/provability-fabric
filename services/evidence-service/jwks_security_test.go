// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"crypto/ed25519"
	"encoding/base64"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/gin-gonic/gin"
)

func postJWKSValidation(t *testing.T, handler http.Handler, endpoint string) int {
	t.Helper()
	payload, err := json.Marshal(map[string]interface{}{
		"raw":      map[string]interface{}{"bundle_id": "test", "sig": "not-a-signature"},
		"jwks_url": endpoint,
	})
	if err != nil {
		t.Fatal(err)
	}
	req := httptest.NewRequest(http.MethodPost, "/api/v1/evidence/validate", bytes.NewReader(payload))
	req.Header.Set("Content-Type", "application/json")
	w := httptest.NewRecorder()
	handler.ServeHTTP(w, req)
	return w.Code
}

func TestCallerJWKSURLCannotCauseOutboundRequest(t *testing.T) {
	var hits atomic.Int64
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		hits.Add(1)
		_, _ = w.Write([]byte(`{"keys":[]}`))
	}))
	defer server.Close()
	gin.SetMode(gin.TestMode)
	service := &EvidenceService{}
	router := gin.New()
	router.POST("/api/v1/evidence/validate", service.verifyCertHandler)

	for _, configured := range []string{
		"",
		server.URL, // Explicit HTTP is still forbidden.
		"https://trusted.example.org/keys",
	} {
		t.Run(configured, func(t *testing.T) {
			t.Setenv("EVIDENCE_TRUSTED_JWKS_URL", configured)
			if status := postJWKSValidation(t, router, server.URL); status != http.StatusBadRequest {
				t.Fatalf("unapproved JWKS URL returned HTTP %d, expected 400", status)
			}
			if count := hits.Load(); count != 0 {
				t.Fatalf("caller-controlled JWKS caused %d outbound requests", count)
			}
		})
	}
}

func TestJWKSApprovalRequiresExactConfiguredHTTPSURL(t *testing.T) {
	for _, invalid := range []string{
		"http://trusted.example.org/jwks",
		"https://user:pass@trusted.example.org/jwks",
		"https://trusted.example.org/jwks#fragment",
		"file:///etc/passwd",
		"//trusted.example.org/jwks",
		"https:///jwks",
	} {
		if err := validateTrustedJWKSURL(invalid); err == nil {
			t.Fatalf("accepted invalid operator trust URL %q", invalid)
		}
	}
	t.Setenv("EVIDENCE_TRUSTED_JWKS_URL", "https://keys.example.org/ed25519.json")
	if err := approveJWKSURL("https://keys.example.org/ed25519.json"); err != nil {
		t.Fatalf("rejected exact trusted URL: %v", err)
	}
	for _, untrusted := range []string{
		"https://keys.example.org/other.json",
		"https://untrusted.example.org/ed25519.json",
		"http://keys.example.org/ed25519.json",
	} {
		if err := approveJWKSURL(untrusted); err == nil {
			t.Fatalf("approved caller-controlled URL %q", untrusted)
		}
	}
	if err := approveJWKSURL(""); err != nil {
		t.Fatalf("network-free PEM diagnostics should still work: %v", err)
	}
}

func TestInvalidConfiguredJWKSEndpointPreventsServiceStartup(t *testing.T) {
	t.Setenv("DATABASE_URL", "")
	t.Setenv("CERT_SIGNER_BACKEND", "")
	t.Setenv("EVIDENCE_STORAGE_PATH", filepath.Join(t.TempDir(), "evidence"))
	for _, invalid := range []string{"http://127.0.0.1:1/keys", "file:///keys"} {
		t.Run(invalid, func(t *testing.T) {
			t.Setenv("EVIDENCE_TRUSTED_JWKS_URL", invalid)
			service, err := NewEvidenceService()
			if service != nil || err == nil || !strings.Contains(err.Error(), "invalid configured evidence JWKS endpoint") {
				t.Fatalf("invalid operator trust endpoint accepted: service=%+v err=%v", service, err)
			}
		})
	}
}

func TestJWKSFetchRejectsPlaintextWithoutOutboundRequest(t *testing.T) {
	var hits atomic.Int64
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		hits.Add(1)
		_, _ = w.Write([]byte(`{"keys":[]}`))
	}))
	defer server.Close()
	if _, err := fetchEd25519KeysFromJWKS(server.URL); err == nil {
		t.Fatal("fetched untrusted plaintext JWKS")
	}
	if hits.Load() != 0 {
		t.Fatal("insecure JWKS request reached a network listener")
	}
}

func TestJWKSFetchLimitsResponseAndRefusesRedirects(t *testing.T) {
	var targetHits atomic.Int64
	target := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		targetHits.Add(1)
		w.WriteHeader(http.StatusOK)
	}))
	defer target.Close()

	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/redirect":
			http.Redirect(w, r, target.URL, http.StatusFound)
		case "/oversize":
			_, _ = w.Write(bytes.Repeat([]byte("x"), 1<<20+1))
		case "/valid":
			seed := make([]byte, ed25519.SeedSize)
			pub := ed25519.NewKeyFromSeed(seed).Public().(ed25519.PublicKey)
			_ = json.NewEncoder(w).Encode(map[string]interface{}{
				"keys": []map[string]string{{
					"kty": "OKP", "crv": "Ed25519",
					"x":   base64.RawURLEncoding.EncodeToString(pub),
					"kid": "disposable-test-root", "use": "sig", "alg": "EdDSA",
				}},
			})
		default:
			w.WriteHeader(http.StatusNotFound)
		}
	}))
	defer server.Close()

	// Trust this disposable TLS fixture only; retain production redirect
	// rejection and deadlines during the network integration test.
	client := server.Client()
	client.Timeout = 3 * time.Second
	client.CheckRedirect = func(*http.Request, []*http.Request) error {
		return http.ErrUseLastResponse
	}
	if _, err := fetchEd25519KeysFromJWKSWithClient(client, server.URL+"/redirect"); err == nil ||
		!strings.Contains(err.Error(), "HTTP 302") {
		t.Fatalf("redirect was accepted or misclassified: %v", err)
	}
	if targetHits.Load() != 0 {
		t.Fatal("JWKS redirect reached its target")
	}
	if _, err := fetchEd25519KeysFromJWKSWithClient(client, server.URL+"/oversize"); err == nil ||
		!strings.Contains(err.Error(), "exceeds 1 MiB") {
		t.Fatalf("unbounded JWKS response was accepted: %v", err)
	}
	pubs, err := fetchEd25519KeysFromJWKSWithClient(client, server.URL+"/valid")
	if err != nil || len(pubs) != 1 || len(pubs[0]) != ed25519.PublicKeySize {
		t.Fatalf("valid disposable Ed25519 JWKS rejected: keys=%d err=%v", len(pubs), err)
	}
}
