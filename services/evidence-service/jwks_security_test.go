// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
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

	for _, configured := range []string{"", "https://trusted.example.org/keys"} {
		t.Run(configured, func(t *testing.T) {
			service.trustedJWKSURL = configured
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
	service := &EvidenceService{trustedJWKSURL: "https://keys.example.org/ed25519.json"}
	if err := service.approveJWKSURL("https://keys.example.org/ed25519.json"); err != nil {
		t.Fatalf("rejected exact trusted URL: %v", err)
	}
	for _, untrusted := range []string{
		"https://keys.example.org/other.json",
		"https://untrusted.example.org/ed25519.json",
		"http://keys.example.org/ed25519.json",
	} {
		if err := service.approveJWKSURL(untrusted); err == nil {
			t.Fatalf("approved caller-controlled URL %q", untrusted)
		}
	}
	if err := service.approveJWKSURL(""); err != nil {
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

func TestJWKSHandlerUsesStartupSnapshotWithoutOutboundRequest(t *testing.T) {
	publicKey, privateKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatalf("generate disposable issuer: %v", err)
	}
	var outbound atomic.Int64
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		outbound.Add(1)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{
			"keys": []map[string]string{{
				"kty": "OKP", "crv": "Ed25519", "kid": "fixture",
				"x": base64.RawURLEncoding.EncodeToString(publicKey),
			}},
		})
	}))
	defer server.Close()
	trustedURL := server.URL + "/keys"
	publicKeys, err := fetchEd25519KeysFromJWKSWithClient(server.Client(), trustedURL)
	if err != nil || len(publicKeys) != 1 {
		t.Fatalf("load disposable verifier key once: keys=%d err=%v", len(publicKeys), err)
	}
	if outbound.Load() != 1 {
		t.Fatalf("expected exactly one startup fetch, got %d", outbound.Load())
	}

	service := &EvidenceService{
		trustedJWKSURL:  trustedURL,
		trustedJWKSKeys: publicKeys,
	}
	gin.SetMode(gin.TestMode)
	router := gin.New()
	router.POST("/api/v1/evidence/validate", service.verifyCertHandler)

	claims := map[string]interface{}{"bundle_id": "test-fixture"}
	canonical, err := marshalCanonicalJSON(claims)
	if err != nil {
		t.Fatal(err)
	}
	issue := func(key ed25519.PrivateKey, endpoint string) CertValidationResponse {
		t.Helper()
		body := map[string]interface{}{
			"raw": map[string]interface{}{
				"bundle_id": "test-fixture",
				"sig":       base64.StdEncoding.EncodeToString(ed25519.Sign(key, canonical)),
			},
			"jwks_url": endpoint,
		}
		encoded, err := json.Marshal(body)
		if err != nil {
			t.Fatal(err)
		}
		req := httptest.NewRequest(http.MethodPost, "/api/v1/evidence/validate", bytes.NewReader(encoded))
		req.Header.Set("Content-Type", "application/json")
		response := httptest.NewRecorder()
		router.ServeHTTP(response, req)
		if response.Code != http.StatusOK {
			t.Fatalf("trusted-key diagnostic returned HTTP %d: %s", response.Code, response.Body.String())
		}
		var decoded CertValidationResponse
		if err := json.Unmarshal(response.Body.Bytes(), &decoded); err != nil {
			t.Fatal(err)
		}
		return decoded
	}
	valid := issue(privateKey, trustedURL)
	if !valid.SignatureChecked || !valid.SignatureValid {
		t.Fatalf("trusted cached key rejected signature: %+v", valid)
	}
	_, wrongKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	forged := issue(wrongKey, trustedURL)
	if !forged.SignatureChecked || forged.SignatureValid {
		t.Fatalf("wrong issuer key accepted: %+v", forged)
	}
	// Even after the operator's remote server changes, validation uses only
	// the initial public-key snapshot. A request never triggers another fetch.
	server.Close()
	cached := issue(privateKey, trustedURL)
	if !cached.SignatureValid || outbound.Load() != 1 {
		t.Fatalf("validation contacted remote JWKS after startup: response=%+v requests=%d", cached, outbound.Load())
	}
}

func TestConfiguredJWKSWithUntrustedTLSFailsStartup(t *testing.T) {
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte(`{"keys":[]}`))
	}))
	defer server.Close()
	t.Setenv("DATABASE_URL", "")
	t.Setenv("CERT_SIGNER_BACKEND", "")
	t.Setenv("EVIDENCE_TRUSTED_JWKS_URL", server.URL)
	storage := filepath.Join(t.TempDir(), "evidence")
	t.Setenv("EVIDENCE_STORAGE_PATH", storage)
	service, err := NewEvidenceService()
	if service != nil || err == nil || !strings.Contains(err.Error(), "load configured evidence JWKS before serving") {
		t.Fatalf("failed to reject unavailable trusted JWKS: service=%+v err=%v", service, err)
	}
	if _, err := os.Stat(storage); !os.IsNotExist(err) {
		t.Fatalf("untrusted JWKS startup created filesystem state: %v", err)
	}
}
