// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

type observedGatewayRequest struct {
	method        string
	path          string
	query         string
	authorization string
	payload       string
}

func TestGatewayProxyPreservesRequestAndBackendStatus(t *testing.T) {
	gin.SetMode(gin.TestMode)
	observed := make(chan observedGatewayRequest, 1)
	backend := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		data, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("read forwarded request: %v", err)
			http.Error(w, "invalid request", http.StatusBadRequest)
			return
		}
		observed <- observedGatewayRequest{
			method:        r.Method,
			path:          r.URL.Path,
			query:         r.URL.RawQuery,
			authorization: r.Header.Get("Authorization"),
			payload:       string(data),
		}
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusAccepted)
		_, _ = io.WriteString(w, `{"ok":true}`)
	}))
	t.Cleanup(backend.Close)
	t.Setenv("PROOF_SERVICE_URL", backend.URL)

	router := gin.New()
	router.NoRoute(NewAPIGateway().routeRequest)
	request := httptest.NewRequest(http.MethodPost, "/api/v1/proofs/run?mode=synthetic", strings.NewReader(`{"test":true}`))
	request.Header.Set("Authorization", "Bearer synthetic-fixture")
	request.Header.Set("Content-Type", "application/json")
	recorder := httptest.NewRecorder()

	router.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusAccepted {
		t.Fatalf("proxy returned HTTP %d: %s", recorder.Code, recorder.Body.String())
	}
	if strings.TrimSpace(recorder.Body.String()) != `{"ok":true}` {
		t.Fatalf("unexpected proxy response: %s", recorder.Body.String())
	}

	select {
	case got := <-observed:
		if got.method != http.MethodPost ||
			got.path != "/api/v1/proofs/run" ||
			got.query != "mode=synthetic" ||
			got.authorization != "Bearer synthetic-fixture" ||
			got.payload != `{"test":true}` {
			t.Fatalf("forwarded request differs from reference: %+v", got)
		}
	default:
		t.Fatal("backend did not observe the request")
	}
}

func TestGatewayRejectsUnmappedAndUnconfiguredUpstreams(t *testing.T) {
	gin.SetMode(gin.TestMode)
	t.Setenv("PROOF_SERVICE_URL", "://invalid-backend")
	router := gin.New()
	router.NoRoute(NewAPIGateway().routeRequest)

	for _, tc := range []struct {
		path   string
		status int
		code   string
	}{
		{"/unmapped-route", http.StatusNotFound, "SERVICE_NOT_FOUND"},
		{"/api/v1/proofs/run", http.StatusServiceUnavailable, ""},
	} {
		recorder := httptest.NewRecorder()
		router.ServeHTTP(recorder, httptest.NewRequest(http.MethodGet, tc.path, nil))
		if recorder.Code != tc.status {
			t.Fatalf("%s returned HTTP %d: %s", tc.path, recorder.Code, recorder.Body.String())
		}
		var response map[string]any
		if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
			t.Fatalf("%s returned invalid JSON: %v", tc.path, err)
		}
		if tc.code != "" {
			detail, ok := response["error"].(map[string]any)
			if !ok || detail["code"] != tc.code {
				t.Fatalf("%s returned unexpected error: %+v", tc.path, response)
			}
		} else if response["service"] != "proof" {
			t.Fatalf("%s returned unexpected service error: %+v", tc.path, response)
		}
	}
}
