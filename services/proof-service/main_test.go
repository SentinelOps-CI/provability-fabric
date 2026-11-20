package main

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

func proofTestRequest() ProofRunRequest {
	return ProofRunRequest{
		PolicyHash: strings.Repeat("a", 64),
		ActionDSL: map[string]any{
			"rules": []any{
				map[string]any{"type": "allow", "role": "researcher"},
			},
		},
	}
}

// TestUnprovedLeanRejectsLegacyCacheAndDoesNotExecute ensures a cached proof
// cannot bypass the admission gate. A disposable executable records invocation
// and exits successfully to model a verifier that accepts a sorry placeholder.
func TestUnprovedLeanRejectsLegacyCacheAndDoesNotExecute(t *testing.T) {
	t.Setenv("PROOF_CACHE_PATH", t.TempDir())
	bin := t.TempDir()
	marker := filepath.Join(t.TempDir(), "lake-invoked")
	script := "#!/bin/sh\nprintf invoked > \"$PROOF_LAKE_SENTINEL\"\nexit 0\n"
	if err := os.WriteFile(filepath.Join(bin, "lake"), []byte(script), 0700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PROOF_LAKE_SENTINEL", marker)
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))

	service := NewProofService()
	req := proofTestRequest()
	service.artifacts[req.PolicyHash] = ProofArtifact{
		Hash:       strings.Repeat("b", 64),
		PolicyHash: req.PolicyHash,
		FilePath:   filepath.Join(t.TempDir(), "obsolete.olean"),
		Verified:   true,
	}
	result, err := service.RunProofs(context.Background(), req)
	if err != nil {
		t.Fatalf("run proofs: %v", err)
	}
	assertUnverified(t, result)

	if _, err := os.Stat(marker); !os.IsNotExist(err) {
		t.Fatalf("Lean executable unexpectedly invoked: stat error = %v", err)
	}
	if len(service.artifacts) != 1 {
		t.Fatal("admission rejection unexpectedly modified the legacy cache")
	}
}

// TestUnprovedMorphNeverSucceeds covers an explicitly enabled Morph mode and
// the internal runner, neither of which carries execution evidence.
func TestUnprovedMorphNeverSucceeds(t *testing.T) {
	t.Setenv("PROOF_CACHE_PATH", t.TempDir())
	t.Setenv("MORPH_ENABLED", "true")
	service := NewProofService()
	req := proofTestRequest()
	req.UseMorph = true
	for name, run := range map[string]func() (*ProofRunResponse, error){
		"public": func() (*ProofRunResponse, error) {
			return service.RunProofs(context.Background(), req)
		},
		"internal": func() (*ProofRunResponse, error) {
			return service.runMorphProofs(req, "theorem assertion : True := by trivial")
		},
	} {
		t.Run(name, func(t *testing.T) {
			result, err := run()
			if err != nil {
				t.Fatalf("run Morph proof: %v", err)
			}
			assertUnverified(t, result)
		})
	}
}

// TestLocalRunnerRejectsAdmittedSource exercises the internal execution
// boundary, not only the HTTP entry point.
func TestLocalRunnerRejectsAdmittedSource(t *testing.T) {
	t.Setenv("PROOF_CACHE_PATH", t.TempDir())
	service := NewProofService()
	for _, tactic := range []string{"sorry", "admit"} {
		t.Run(tactic, func(t *testing.T) {
			source := "theorem placeholder : True := by\n  " + tactic + "\n"
			resp, err := service.runLocalProofs(proofTestRequest(), source)
			if err != nil {
				t.Fatal(err)
			}
			assertUnverified(t, resp)
		})
	}
}

func TestHTTPProofResultIsNotPresentedAsVerified(t *testing.T) {
	t.Setenv("PROOF_CACHE_PATH", t.TempDir())
	gin.SetMode(gin.TestMode)
	service := NewProofService()
	router := gin.New()
	router.POST("/api/v1/proofs/run", service.runProofsHandler)

	req := proofTestRequest()
	body, err := json.Marshal(req)
	if err != nil {
		t.Fatal(err)
	}
	httpReq := httptest.NewRequest(http.MethodPost, "/api/v1/proofs/run", strings.NewReader(string(body)))
	httpReq.Header.Set("Content-Type", "application/json")
	rec := httptest.NewRecorder()
	router.ServeHTTP(rec, httpReq)
	if rec.Code != http.StatusUnprocessableEntity {
		t.Fatalf("unverified proof: HTTP %d, want 422: %s", rec.Code, rec.Body.String())
	}

	var result ProofRunResponse
	if err := json.Unmarshal(rec.Body.Bytes(), &result); err != nil {
		t.Fatalf("decode proof result: %v", err)
	}
	assertUnverified(t, &result)
}

func TestMalformedRuleDoesNotProduceProof(t *testing.T) {
	t.Setenv("PROOF_CACHE_PATH", t.TempDir())
	gin.SetMode(gin.TestMode)
	router := gin.New()
	service := NewProofService()
	router.POST("/api/v1/proofs/run", service.runProofsHandler)
	req := proofTestRequest()
	req.ActionDSL = map[string]any{"rules": []any{map[string]any{"role": "researcher"}}}
	body, err := json.Marshal(req)
	if err != nil {
		t.Fatal(err)
	}
	httpReq := httptest.NewRequest(http.MethodPost, "/api/v1/proofs/run", strings.NewReader(string(body)))
	httpReq.Header.Set("Content-Type", "application/json")
	rec := httptest.NewRecorder()
	router.ServeHTTP(rec, httpReq)
	if rec.Code != http.StatusBadRequest {
		t.Fatalf("malformed rule: HTTP %d, want 400; response = %s", rec.Code, rec.Body.String())
	}
}

func assertUnverified(t *testing.T, result *ProofRunResponse) {
	t.Helper()
	if result == nil || result.Status != "failed" || result.ProofHash != "" ||
		len(result.Artifacts) != 0 || len(result.ArtifactIndex) != 0 {
		t.Fatalf("unverified result issued proof evidence: %#v", result)
	}
	if len(result.Diagnostics) == 0 || result.Diagnostics[0].Level != "error" {
		t.Fatalf("unverified result lacks error diagnostics: %#v", result.Diagnostics)
	}
}
