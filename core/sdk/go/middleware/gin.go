// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package middleware

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/provability-fabric/core/sdk/go/sdk"
)

// PFMiddlewareOptions holds configuration for the PF middleware
type PFMiddlewareOptions struct {
	SDK         *sdk.SDK
	AddHeaders  bool
	VerifyTrace bool
	Timeout     time.Duration
}

// PFMiddleware adds Provability Fabric headers and verification to Gin
func PFMiddleware(options PFMiddlewareOptions) gin.HandlerFunc {
	if options.Timeout == 0 {
		options.Timeout = 5 * time.Second
	}

	return func(c *gin.Context) {
		// Add PF-Sig headers
		if options.AddHeaders {
			requestID := c.GetHeader("X-Request-ID")
			if requestID == "" {
				requestID = generateRequestID()
			}

			c.Header("PF-Sig-Version", "1.0")
			c.Header("PF-Sig-Timestamp", time.Now().UTC().Format(time.RFC3339))
			c.Header("PF-Sig-Request-ID", requestID)
		}

		// Verify trace if requested
		if options.VerifyTrace && options.SDK != nil {
			var traceData map[string]interface{}
			if err := c.ShouldBindJSON(&traceData); err == nil {
				if trace, ok := traceData["trace"]; ok {
					// Convert to Trace struct and verify
					traceBytes, _ := json.Marshal(trace)
					var traceObj sdk.Trace
					if err := json.Unmarshal(traceBytes, &traceObj); err == nil {
						ctx, cancel := context.WithTimeout(c.Request.Context(), options.Timeout)
						defer cancel()

						result, err := options.SDK.VerifyTrace(ctx, &traceObj)
						if err != nil {
							c.JSON(http.StatusBadRequest, gin.H{
								"error":   "Trace verification failed",
								"details": err.Error(),
							})
							c.Abort()
							return
						}

						if !result.Valid {
							c.JSON(http.StatusBadRequest, gin.H{
								"error":   "Invalid trace",
								"details": "Trace validation failed",
							})
							c.Abort()
							return
						}
					}
				}
			}
		}

		c.Next()
	}
}

// CircuitBreakerMiddleware provides circuit breaker functionality
func CircuitBreakerMiddleware(options CircuitBreakerOptions) gin.HandlerFunc {
	cb := newCircuitBreaker(options)

	return func(c *gin.Context) {
		if !cb.AllowRequest() {
			c.JSON(http.StatusServiceUnavailable, gin.H{
				"error":   "Service temporarily unavailable",
				"details": "Circuit breaker is open",
			})
			c.Abort()
			return
		}

		// Track response status
		c.Next()

		if c.Writer.Status() >= 500 {
			cb.RecordFailure()
		} else {
			cb.RecordSuccess()
		}
	}
}

// RetryMiddleware provides retry functionality with exponential backoff
func RetryMiddleware(options RetryOptions) gin.HandlerFunc {
	return func(c *gin.Context) {
		var lastErr error
		for attempt := 0; attempt <= options.MaxRetries; attempt++ {
			// Store original response writer
			originalWriter := c.Writer
			responseRecorder := &responseRecorder{
				ResponseWriter: originalWriter,
				statusCode:     200,
			}
			c.Writer = responseRecorder

			// Execute the request
			c.Next()

			// Check if we need to retry
			if responseRecorder.statusCode < 500 || attempt == options.MaxRetries {
				// Restore original writer and copy response
				c.Writer = originalWriter
				copyResponse(originalWriter, responseRecorder)
				return
			}

			lastErr = fmt.Errorf("request failed with status %d", responseRecorder.statusCode)

			// Calculate delay for next attempt
			delay := options.BaseDelay
			for i := 0; i < attempt; i++ {
				delay *= 2
				if delay > options.MaxDelay {
					delay = options.MaxDelay
					break
				}
			}

			// Wait before retry
			time.Sleep(delay)
		}

		// All retries failed
		c.JSON(http.StatusInternalServerError, gin.H{
			"error":   "Request failed after retries",
			"details": lastErr.Error(),
		})
		c.Abort()
	}
}

// CircuitBreakerOptions holds circuit breaker configuration
type CircuitBreakerOptions struct {
	FailureThreshold int
	ResetTimeout     time.Duration
	MonitoringWindow time.Duration
}

// RetryOptions holds retry configuration
type RetryOptions struct {
	MaxRetries int
	BaseDelay  time.Duration
	MaxDelay   time.Duration
}

// circuitBreaker implements the circuit breaker pattern
type circuitBreaker struct {
	failureCount    int
	lastFailureTime time.Time
	isOpen          bool
	options         CircuitBreakerOptions
}

func newCircuitBreaker(options CircuitBreakerOptions) *circuitBreaker {
	if options.FailureThreshold == 0 {
		options.FailureThreshold = 5
	}
	if options.ResetTimeout == 0 {
		options.ResetTimeout = 60 * time.Second
	}

	return &circuitBreaker{
		options: options,
	}
}

func (cb *circuitBreaker) AllowRequest() bool {
	if cb.isOpen {
		if time.Since(cb.lastFailureTime) > cb.options.ResetTimeout {
			cb.isOpen = false
			cb.failureCount = 0
		} else {
			return false
		}
	}
	return true
}

func (cb *circuitBreaker) RecordFailure() {
	cb.failureCount++
	cb.lastFailureTime = time.Now()
	if cb.failureCount >= cb.options.FailureThreshold {
		cb.isOpen = true
	}
}

func (cb *circuitBreaker) RecordSuccess() {
	cb.failureCount = 0
}

// responseRecorder captures response details for retry logic
type responseRecorder struct {
	gin.ResponseWriter
	statusCode int
}

func (r *responseRecorder) WriteHeader(code int) {
	r.statusCode = code
	r.ResponseWriter.WriteHeader(code)
}

func (r *responseRecorder) Write(data []byte) (int, error) {
	return r.ResponseWriter.Write(data)
}

func (r *responseRecorder) WriteString(s string) (int, error) {
	return r.ResponseWriter.WriteString(s)
}

func generateRequestID() string {
	return fmt.Sprintf("req_%d_%s", time.Now().UnixNano(), randomString(9))
}

func randomString(length int) string {
	const charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
	b := make([]byte, length)
	for i := range b {
		b[i] = charset[time.Now().UnixNano()%int64(len(charset))]
	}
	return string(b)
}

func copyResponse(dst gin.ResponseWriter, src *responseRecorder) {
	// This is a simplified copy - in practice, you'd want to copy headers and body
	dst.WriteHeader(src.statusCode)
}
