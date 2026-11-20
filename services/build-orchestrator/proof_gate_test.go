package main

import (
	"context"
	"encoding/json"
	"errors"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

func buildTestRequest() PolicyBuildRequest {
	return PolicyBuildRequest{
		PolicyHash: strings.Repeat("a", 64),
		ProofHash:  strings.Repeat("b", 64),
		ActionDSL: map[string]interface{}{
			"rules": []interface{}{
				map[string]interface{}{
					"rule_id": "r1",
					"type":    "allow",
					"role":    "researcher",
				},
			},
		},
	}
}

// TestNoTrustedVerifierCannotIssueBuild demonstrates that an unverified
// caller-supplied proof hash is insufficient for issuing build artifacts.
func TestNoTrustedVerifierCannotIssueBuild(t *testing.T) {
	dir := t.TempDir()
	t.Setenv("BUILD_CACHE_PATH", dir)
	service := NewBuildOrchestrator()
	result, err := service.BuildPolicy(context.Background(), buildTestRequest())
	if !errors.Is(err, errProofVerifierUnavailable) || result != nil {
		t.Fatalf("untrusted proof was accepted: result=%#v, err=%v", result, err)
	}
	if len(service.builds) != 0 {
		t.Fatal("untrusted proof created a build")
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("untrusted proof generated %d artifacts", len(entries))
	}
}

// TestCallerSigningKeyCannotIssueFakeSignature pins rejection of the prior
// signature-shaped SHA-256 digest, which ignored the supplied signing key.
func TestCallerSigningKeyCannotIssueFakeSignature(t *testing.T) {
	t.Setenv("BUILD_CACHE_PATH", t.TempDir())
	service := NewBuildOrchestrator()
	req := buildTestRequest()
	req.SigningKey = "disposable-test-key"
	result, err := service.BuildPolicy(context.Background(), req)
	if !errors.Is(err, errBuildSigningUnavailable) || result != nil {
		t.Fatalf("unsupported signature was accepted: result=%#v, err=%v", result, err)
	}
	if len(service.builds) != 0 {
		t.Fatal("unsupported signing created a build")
	}
}

// rejectingProofVerifier is exclusively a negative test fixture. It is
// deliberately not an authentication or production-proof implementation.
type rejectingProofVerifier struct {
	seen  bool
	claim ProofEvidenceClaim
}

func (v *rejectingProofVerifier) Verify(_ context.Context, claim ProofEvidenceClaim) error {
	v.seen = true
	v.claim = claim
	return errors.New("untrusted proof artifact")
}

func TestRejectedProofEvidenceCannotIssueBuild(t *testing.T) {
	dir := t.TempDir()
	t.Setenv("BUILD_CACHE_PATH", dir)
	service := NewBuildOrchestrator()
	verifier := &rejectingProofVerifier{}
	service.proofVerifier = verifier
	req := buildTestRequest()
	result, err := service.BuildPolicy(context.Background(), req)
	if !errors.Is(err, errProofEvidenceRejected) || result != nil {
		t.Fatalf("rejected proof generated build: result=%#v, err=%v", result, err)
	}
	if !verifier.seen || verifier.claim.PolicyHash != req.PolicyHash ||
		verifier.claim.ProofHash != req.ProofHash {
		t.Fatalf("verifier did not receive bound claim: %+v", verifier.claim)
	}
	var source map[string]interface{}
	if err := json.Unmarshal(verifier.claim.ActionDSLJSON, &source); err != nil {
		t.Fatalf("decode verifier input: %v", err)
	}
	if _, ok := source["rules"].([]interface{}); !ok {
		t.Fatalf("verifier received wrong policy content: %#v", source)
	}
	if len(service.builds) != 0 {
		t.Fatal("rejected proof created a build")
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("rejected proof generated %d artifacts", len(entries))
	}
}

func TestHTTPBuildProofAndSigningFailClosed(t *testing.T) {
	t.Setenv("BUILD_CACHE_PATH", t.TempDir())
	gin.SetMode(gin.TestMode)
	service := NewBuildOrchestrator()
	router := gin.New()
	router.POST("/api/v1/policy/build", service.buildPolicyHandler)
	router.GET("/api/v1/builds", service.listBuildsHandler)

	post := func(req PolicyBuildRequest, wantStatus int) {
		t.Helper()
		body, err := json.Marshal(req)
		if err != nil {
			t.Fatal(err)
		}
		r := httptest.NewRequest(http.MethodPost, "/api/v1/policy/build", strings.NewReader(string(body)))
		r.Header.Set("Content-Type", "application/json")
		w := httptest.NewRecorder()
		router.ServeHTTP(w, r)
		if w.Code != wantStatus {
			t.Fatalf("POST /policy/build: HTTP %d, want %d: %s", w.Code, wantStatus, w.Body.String())
		}
		var data map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &data); err != nil {
			t.Fatalf("decode rejected build: %v", err)
		}
		if _, hasBuild := data["build_id"]; hasBuild {
			t.Fatalf("rejected build issued a build id: %#v", data)
		}
		if _, hasSignature := data["signature"]; hasSignature {
			t.Fatalf("rejected build issued a signature: %#v", data)
		}
	}

	post(buildTestRequest(), http.StatusServiceUnavailable)
	req := buildTestRequest()
	req.SigningKey = "unsupported-caller-key"
	post(req, http.StatusNotImplemented)

	// Even a configured verifier must reject invalid proof artifacts.
	service.proofVerifier = &rejectingProofVerifier{}
	post(buildTestRequest(), http.StatusUnprocessableEntity)

	r := httptest.NewRequest(http.MethodGet, "/api/v1/builds", nil)
	w := httptest.NewRecorder()
	router.ServeHTTP(w, r)
	if w.Code != http.StatusOK {
		t.Fatalf("list builds: HTTP %d: %s", w.Code, w.Body.String())
	}
	var listed map[string]interface{}
	if err := json.Unmarshal(w.Body.Bytes(), &listed); err != nil {
		t.Fatal(err)
	}
	if count, ok := listed["count"].(float64); !ok || count != 0 {
		t.Fatalf("unverified requests issued builds: %#v", listed)
	}
}
