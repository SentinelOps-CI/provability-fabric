// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

// A compliance packet is currently an in-request JSON diagnostic. The
// service has no authenticated durable store mapping packet IDs to archives.
// Returning a synthetic ZIP would fabricate certificate and audit evidence.
func TestCompliancePacketDownloadFailsClosedWithoutPersistedPacket(t *testing.T) {
	gin.SetMode(gin.TestMode)
	storage := t.TempDir()
	credential, token := evidenceTestCredential(t, "disposable-tenant", true, false)
	service := &EvidenceService{storagePath: storage, access: []evidenceCredential{credential}}
	router := gin.New()
	router.POST("/api/v1/compliance/packet", service.buildPacketHandler)
	router.GET("/api/v1/compliance/packet/:id", service.downloadPacketHandler)

	build := httptest.NewRequest(http.MethodPost, "/api/v1/compliance/packet",
		bytes.NewBufferString(`{"tenant_id":"disposable-tenant"}`))
	build.Header.Set("Content-Type", "application/json")
	build.Header.Set("Authorization", token)
	built := httptest.NewRecorder()
	router.ServeHTTP(built, build)
	if built.Code != http.StatusOK {
		t.Fatalf("existing JSON diagnostic failed: HTTP %d: %s", built.Code, built.Body.String())
	}
	var packet struct {
		PacketID string `json:"packet_id"`
	}
	if err := json.Unmarshal(built.Body.Bytes(), &packet); err != nil {
		t.Fatalf("decode JSON diagnostic: %v", err)
	}
	if packet.PacketID == "" {
		t.Fatal("JSON diagnostic omitted its non-persistent packet identifier")
	}

	for _, id := range []string{packet.PacketID, "unknown-packet-id"} {
		t.Run(id, func(t *testing.T) {
			request := httptest.NewRequest(http.MethodGet, "/api/v1/compliance/packet/"+id, nil)
			response := httptest.NewRecorder()
			router.ServeHTTP(response, request)
			if response.Code != http.StatusNotImplemented {
				t.Fatalf("fabricated export was not refused: HTTP %d: %s",
					response.Code, response.Body.String())
			}
			if !strings.HasPrefix(response.Header().Get("Content-Type"), "application/json") {
				t.Fatalf("unavailable export did not return JSON: %q",
					response.Header().Get("Content-Type"))
			}
			if response.Header().Get("Content-Disposition") != "" {
				t.Fatal("unavailable export advertised a downloadable archive")
			}
			var result struct {
				Error struct {
					Code string `json:"code"`
				} `json:"error"`
			}
			if err := json.Unmarshal(response.Body.Bytes(), &result); err != nil {
				t.Fatalf("decode failure response: %v", err)
			}
			if result.Error.Code != "PACKET_EXPORT_UNAVAILABLE" {
				t.Fatalf("wrong failure code: %q", result.Error.Code)
			}
		})
	}
	entries, err := os.ReadDir(storage)
	if err != nil {
		t.Fatalf("inspect evidence directory: %v", err)
	}
	if len(entries) != 0 {
		t.Fatalf("diagnostic and refused downloads created %d unexpected files", len(entries))
	}
}
