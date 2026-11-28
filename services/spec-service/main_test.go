package main

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"

	"github.com/gin-gonic/gin"
)

// TestCompilePolicyOwnsMetadata verifies that compiling a policy never
// modifies the caller's map or retains a mutable alias to that input.
func TestCompilePolicyOwnsMetadata(t *testing.T) {
	service := NewSpecService()
	input := map[string]string{"origin": "caller"}

	response, err := service.CompilePolicy(context.Background(), PolicyCompileRequest{
		English:  "allow analyst to read report when role is analyst",
		PolicyID: "metadata-contract",
		Metadata: input,
	})
	if err != nil {
		t.Fatalf("compile policy: %v", err)
	}
	if _, exists := input["compiled_at"]; exists {
		t.Fatal("compiler metadata leaked into caller's map")
	}
	if _, exists := input["compiler_version"]; exists {
		t.Fatal("compiler version leaked into caller's map")
	}
	if response.ActionDSL.Metadata["origin"] != "caller" {
		t.Fatalf("unexpected compiled metadata: %#v", response.ActionDSL.Metadata)
	}

	input["origin"] = "mutated-by-caller"
	service.mu.RLock()
	storedOrigin := service.policies["metadata-contract"].Metadata["origin"]
	service.mu.RUnlock()
	if storedOrigin != "caller" {
		t.Fatalf("stored metadata changed through caller alias: %q", storedOrigin)
	}
}

// TestConcurrentHTTPPolicyAccess executes actual handlers concurrently under
// Go's race detector. It exercises write/write and write/read interference.
func TestConcurrentHTTPPolicyAccess(t *testing.T) {
	gin.SetMode(gin.TestMode)
	service := NewSpecService()
	router := gin.New()
	router.POST("/api/v1/policy/compile", service.compileHandler)
	router.GET("/api/v1/policy/:id", service.getPolicyHandler)
	router.GET("/api/v1/policies", service.listPoliciesHandler)
	router.GET("/api/v1/health", service.healthHandler)

	const writers = 64
	errors := make(chan error, writers*4)
	var wg sync.WaitGroup

	for i := 0; i < writers; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			policyID := fmt.Sprintf("concurrent-%d", i)
			requestBody := fmt.Sprintf(
				`{"english":"allow analyst to read report when role is analyst","policy_id":%q}`,
				policyID,
			)
			req := httptest.NewRequest(http.MethodPost, "/api/v1/policy/compile", strings.NewReader(requestBody))
			req.Header.Set("Content-Type", "application/json")
			rec := httptest.NewRecorder()
			router.ServeHTTP(rec, req)
			if rec.Code != http.StatusOK {
				errors <- fmt.Errorf("compile %s: HTTP %d: %s", policyID, rec.Code, rec.Body.String())
				return
			}

			for _, path := range []string{
				"/api/v1/policy/" + policyID,
				"/api/v1/policies",
				"/api/v1/health",
			} {
				req := httptest.NewRequest(http.MethodGet, path, nil)
				rec := httptest.NewRecorder()
				router.ServeHTTP(rec, req)
				if rec.Code != http.StatusOK {
					errors <- fmt.Errorf("GET %s: HTTP %d: %s", path, rec.Code, rec.Body.String())
				}
			}
		}(i)
	}

	wg.Wait()
	close(errors)
	for err := range errors {
		t.Error(err)
	}

	rec := httptest.NewRecorder()
	router.ServeHTTP(rec, httptest.NewRequest(http.MethodGet, "/api/v1/policies", nil))
	if rec.Code != http.StatusOK {
		t.Fatalf("list policies: HTTP %d: %s", rec.Code, rec.Body.String())
	}
	var result struct {
		Count int `json:"count"`
	}
	if err := json.Unmarshal(rec.Body.Bytes(), &result); err != nil {
		t.Fatalf("decode policy list: %v", err)
	}
	if result.Count != writers {
		t.Fatalf("policy count = %d, want %d", result.Count, writers)
	}
}
