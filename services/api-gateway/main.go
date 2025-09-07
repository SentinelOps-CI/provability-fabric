// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"fmt"
	"log"
	"net/http"
	"net/http/httputil"
	"net/url"
	"os"
	"strings"
	"time"

	"github.com/gin-contrib/cors"
	"github.com/gin-gonic/gin"
)

// ServiceConfig represents configuration for a backend service
type ServiceConfig struct {
	Name       string
	URL        string
	Path       string
	HealthPath string
}

// APIGateway handles routing to backend services
type APIGateway struct {
	services         map[string]ServiceConfig
	proxies          map[string]*httputil.ReverseProxy
	telemetryEnabled bool
	firstInitAt      time.Time
	firstCertAt      time.Time
	currentEpoch     int
}

// NewAPIGateway creates a new API gateway instance
func NewAPIGateway() *APIGateway {
	services := map[string]ServiceConfig{
		"spec": {
			Name:       "spec-service",
			URL:        getEnvOrDefault("SPEC_SERVICE_URL", "http://localhost:8001"),
			Path:       "/api/v1/policy",
			HealthPath: "/api/v1/health",
		},
		"proof": {
			Name:       "proof-service",
			URL:        getEnvOrDefault("PROOF_SERVICE_URL", "http://localhost:8002"),
			Path:       "/api/v1/proofs",
			HealthPath: "/api/v1/health",
		},
		"build": {
			Name:       "build-orchestrator",
			URL:        getEnvOrDefault("BUILD_SERVICE_URL", "http://localhost:8003"),
			Path:       "/api/v1/policy/build",
			HealthPath: "/api/v1/health",
		},
		"evidence": {
			Name:       "evidence-service",
			URL:        getEnvOrDefault("EVIDENCE_SERVICE_URL", "http://localhost:8004"),
			Path:       "/api/v1/evidence",
			HealthPath: "/api/v1/health",
		},
		"replay": {
			Name:       "replay-service",
			URL:        getEnvOrDefault("REPLAY_SERVICE_URL", "http://localhost:8005"),
			Path:       "/api/v1/replay",
			HealthPath: "/api/v1/health",
		},
		"runtime": {
			Name:       "runtime-service",
			URL:        getEnvOrDefault("RUNTIME_SERVICE_URL", "http://localhost:8006"),
			Path:       "/api/v1/runtime",
			HealthPath: "/api/v1/health",
		},
	}

	proxies := make(map[string]*httputil.ReverseProxy)
	for key, service := range services {
		target, err := url.Parse(service.URL)
		if err != nil {
			log.Printf("Warning: Invalid URL for service %s: %v", service.Name, err)
			continue
		}
		proxies[key] = httputil.NewSingleHostReverseProxy(target)
	}

	telemetryDefault := strings.EqualFold(getEnvOrDefault("TELEMETRY_DEFAULT_ENABLED", "false"), "true")

	return &APIGateway{
		services:         services,
		proxies:          proxies,
		telemetryEnabled: telemetryDefault,
		currentEpoch:     42,
	}
}

// routeRequest routes requests to appropriate backend services
func (gw *APIGateway) routeRequest(c *gin.Context) {
	path := c.Request.URL.Path

	// Route based on path patterns
	var serviceKey string
	var targetPath string

	switch {
	case strings.HasPrefix(path, "/api/v1/policy/compile") || strings.HasPrefix(path, "/api/v1/policies"):
		serviceKey = "spec"
		targetPath = path
	case strings.HasPrefix(path, "/api/v1/proofs") || strings.HasPrefix(path, "/api/v1/artifacts"):
		serviceKey = "proof"
		targetPath = path
	case strings.HasPrefix(path, "/api/v1/policy/build") || strings.HasPrefix(path, "/api/v1/builds"):
		serviceKey = "build"
		targetPath = path
	case strings.HasPrefix(path, "/api/v1/evidence") || strings.HasPrefix(path, "/api/v1/compliance"):
		serviceKey = "evidence"
		targetPath = path
	case strings.HasPrefix(path, "/api/v1/replay"):
		serviceKey = "replay"
		targetPath = path
	case strings.HasPrefix(path, "/api/v1/runtime"):
		serviceKey = "runtime"
		targetPath = path
	default:
		writeError(c, http.StatusNotFound, "SERVICE_NOT_FOUND", "No backend matched the path", "Check URL or service path prefix", "https://docs.sentinelops.dev/error-catalog#SERVICE_NOT_FOUND")
		return
	}

	// Get proxy for service
	proxy, exists := gw.proxies[serviceKey]
	if !exists {
		c.JSON(http.StatusServiceUnavailable, gin.H{
			"error":   "Service unavailable",
			"service": serviceKey,
		})
		return
	}

	// Update request path
	c.Request.URL.Path = targetPath

	// Proxy the request
	proxy.ServeHTTP(c.Writer, c.Request)
}

// healthHandler provides aggregated health status
func (gw *APIGateway) healthHandler(c *gin.Context) {
	health := map[string]interface{}{
		"status":    "healthy",
		"service":   "api-gateway",
		"version":   "1.0.0",
		"timestamp": time.Now(),
		"services":  make(map[string]interface{}),
		"telemetry": map[string]any{"enabled": gw.telemetryEnabled},
	}

	// Check health of all backend services
	overallHealthy := true
	for key, service := range gw.services {
		serviceHealth := gw.checkServiceHealth(service)
		health["services"].(map[string]interface{})[key] = serviceHealth

		if serviceHealth.(map[string]interface{})["status"] != "healthy" {
			overallHealthy = false
		}
	}

	if !overallHealthy {
		health["status"] = "degraded"
	}

	statusCode := http.StatusOK
	if !overallHealthy {
		statusCode = http.StatusServiceUnavailable
	}

	c.JSON(statusCode, health)
}

// checkServiceHealth checks the health of a backend service
func (gw *APIGateway) checkServiceHealth(service ServiceConfig) interface{} {
	client := &http.Client{Timeout: 5 * time.Second}

	resp, err := client.Get(service.URL + service.HealthPath)
	if err != nil {
		return map[string]interface{}{
			"status": "unhealthy",
			"error":  err.Error(),
		}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusOK {
		return map[string]interface{}{
			"status": "healthy",
			"url":    service.URL,
		}
	}

	return map[string]interface{}{
		"status":      "unhealthy",
		"status_code": resp.StatusCode,
		"url":         service.URL,
	}
}

// metricsHandler provides aggregated metrics
func (gw *APIGateway) metricsHandler(c *gin.Context) {
	// Aggregate metrics from all services
	metrics := map[string]interface{}{
		"gateway": map[string]interface{}{
			"requests_total":   0, // Would track actual requests
			"response_time_ms": 0, // Would track actual response times
			"errors_total":     0, // Would track actual errors
		},
		"services": make(map[string]interface{}),
	}

	c.JSON(http.StatusOK, metrics)
}

// Runtime service endpoints (inline for simplicity)
func (gw *APIGateway) setupRuntimeEndpoints(r *gin.Engine) {
	runtime := r.Group("/api/v1/runtime")
	{
		runtime.POST("/deploy", gw.deployPolicyHandler)
		runtime.POST("/epoch/rotate", gw.rotateEpochHandler)
		runtime.GET("/slo", gw.getSLOHandler)
		runtime.GET("/health", gw.runtimeHealthHandler)
	}
}

// Telemetry endpoints (inline)
func (gw *APIGateway) setupTelemetryEndpoints(r *gin.Engine) {
	tele := r.Group("/api/v1/telemetry")
	{
		tele.GET("/opt", func(c *gin.Context) {
			c.JSON(http.StatusOK, gin.H{"enabled": gw.telemetryEnabled})
		})
		tele.POST("/opt", func(c *gin.Context) {
			var req struct {
				Enabled bool `json:"enabled"`
			}
			if err := c.ShouldBindJSON(&req); err != nil {
				c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
				return
			}
			gw.telemetryEnabled = req.Enabled
			c.JSON(http.StatusOK, gin.H{"ok": true, "enabled": gw.telemetryEnabled})
		})
		tele.POST("/event", func(c *gin.Context) {
			if !gw.telemetryEnabled {
				c.JSON(http.StatusOK, gin.H{"ok": true, "skipped": true})
				return
			}
			var payload map[string]any
			if err := c.ShouldBindJSON(&payload); err != nil {
				c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
				return
			}
			// Minimal redaction: drop obvious PII keys if present
			delete(payload, "user")
			delete(payload, "email")
			delete(payload, "token")
			// Best-effort scrubbing in nested data
			if data, ok := payload["data"].(map[string]any); ok {
				for k, v := range data {
					lk := strings.ToLower(k)
					if strings.Contains(lk, "email") || strings.Contains(lk, "token") || strings.Contains(lk, "secret") || strings.Contains(lk, "user") {
						delete(data, k)
						continue
					}
					if s, ok := v.(string); ok {
						data[k] = redactPIIString(s)
					}
				}
				payload["data"] = data
			}

			// Compute time-to-first-cert (init -> first_valid_cert)
			if t, ok := payload["type"].(string); ok {
				now := time.Now()
				if t == "init" && gw.firstInitAt.IsZero() {
					gw.firstInitAt = now
				}
				if t == "first_valid_cert" && gw.firstCertAt.IsZero() {
					gw.firstCertAt = now
					if !gw.firstInitAt.IsZero() {
						delta := gw.firstCertAt.Sub(gw.firstInitAt)
						log.Printf("telemetry metric time_to_first_cert_ms=%d", delta.Milliseconds())
					}
				}
			}

			log.Printf("telemetry event: %v", payload)
			c.JSON(http.StatusOK, gin.H{"ok": true})
		})
	}
}

func (gw *APIGateway) deployPolicyHandler(c *gin.Context) {
	var req struct {
		PolicyHash   string `json:"policy_hash" binding:"required"`
		AutomataHash string `json:"automata_hash" binding:"required"`
		Epoch        int    `json:"epoch" binding:"required"`
	}

	if err := c.ShouldBindJSON(&req); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_REQUEST", err.Error(), "Fix request body and retry", "https://docs.sentinelops.dev/error-catalog#INVALID_REQUEST")
		return
	}

	// Simulate deployment
	c.JSON(http.StatusOK, gin.H{
		"policy_hash":   req.PolicyHash,
		"automata_hash": req.AutomataHash,
		"epoch":         req.Epoch,
		"status":        "deployed",
		"deployed_at":   time.Now(),
	})
	// Track current epoch
	gw.currentEpoch = req.Epoch
}

func (gw *APIGateway) rotateEpochHandler(c *gin.Context) {
	var req struct {
		OldEpoch int    `json:"old_epoch" binding:"required"`
		NewEpoch int    `json:"new_epoch" binding:"required"`
		Reason   string `json:"reason,omitempty"`
	}

	if err := c.ShouldBindJSON(&req); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_REQUEST", err.Error(), "Fix request body and retry", "https://docs.sentinelops.dev/error-catalog#INVALID_REQUEST")
		return
	}

	c.JSON(http.StatusOK, gin.H{
		"old_epoch":  req.OldEpoch,
		"new_epoch":  req.NewEpoch,
		"rotated_at": time.Now(),
		"rotated_by": "api-gateway", // Would be actual user
		"reason":     req.Reason,
	})
	gw.currentEpoch = req.NewEpoch
}

func (gw *APIGateway) getSLOHandler(c *gin.Context) {
	// Mock SLO data
	c.JSON(http.StatusOK, gin.H{
		"epoch": gw.currentEpoch,
		"latency": map[string]interface{}{
			"p50": 1.2,
			"p95": 2.1,
			"p99": 4.3,
		},
		"tps":                      1250,
		"error_rate":               0.02,
		"cert_validation_failures": 0,
		"sidecar_decision_latency": 1.8,
		"egress_write_latency":     0.9,
		"timestamp":                time.Now(),
	})
}

func (gw *APIGateway) runtimeHealthHandler(c *gin.Context) {
	c.JSON(http.StatusOK, gin.H{
		"status":    "healthy",
		"service":   "runtime-service",
		"version":   "1.0.0",
		"timestamp": time.Now(),
	})
}

func getEnvOrDefault(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

// redactPIIString performs coarse redaction for emails and tokens inside strings
func redactPIIString(s string) string {
	// redact email-like substrings
	if strings.Contains(s, "@") {
		return "[REDACTED_EMAIL]"
	}
	ls := strings.ToLower(s)
	if strings.HasPrefix(ls, "bearer ") {
		return "Bearer [REDACTED]"
	}
	if strings.HasPrefix(s, "sk-") || strings.HasPrefix(s, "pk_") {
		return "[REDACTED_KEY]"
	}
	return s
}

// writeError returns a standardized error envelope
func writeError(c *gin.Context, status int, code, cause, action, docs string) {
	c.JSON(status, gin.H{
		"error": gin.H{
			"code":     code,
			"cause":    cause,
			"action":   action,
			"docs_url": docs,
		},
	})
}

func main() {
	// Initialize gateway
	gateway := NewAPIGateway()

	// Set up Gin router
	r := gin.Default()

	// CORS configuration
	config := cors.DefaultConfig()
	config.AllowOrigins = []string{"*"}
	config.AllowMethods = []string{"GET", "POST", "PUT", "DELETE", "OPTIONS"}
	config.AllowHeaders = []string{"Origin", "Content-Type", "Accept", "Authorization"}
	r.Use(cors.New(config))

	// Request logging middleware
	r.Use(gin.LoggerWithFormatter(func(param gin.LogFormatterParams) string {
		return fmt.Sprintf("%s - [%s] \"%s %s %s %d %s \"%s\" %s\n",
			param.ClientIP,
			param.TimeStamp.Format(time.RFC1123),
			param.Method,
			param.Path,
			param.Request.Proto,
			param.StatusCode,
			param.Latency,
			param.Request.UserAgent(),
			param.ErrorMessage,
		)
	}))

	// Gateway-level endpoints
	r.GET("/health", gateway.healthHandler)
	r.GET("/metrics", gateway.metricsHandler)

	// Setup inline endpoints
	gateway.setupRuntimeEndpoints(r)
	gateway.setupTelemetryEndpoints(r)

	// Route all other API requests to backend services
	r.NoRoute(gateway.routeRequest)

	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8000"
	}

	log.Printf("API Gateway starting on port %s", port)
	log.Printf("Routing to services:")
	for key, service := range gateway.services {
		log.Printf("  %s: %s -> %s", key, service.Path, service.URL)
	}

	log.Fatal(r.Run(":" + port))
}
