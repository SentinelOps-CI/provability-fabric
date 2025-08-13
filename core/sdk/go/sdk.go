// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package sdk

import (
	"context"
	"fmt"
	"time"
)

// SDK represents the main Provability Fabric SDK
type SDK struct {
	client Client
	config Config
}

// Config holds SDK configuration
type Config struct {
	Endpoint       string               `json:"endpoint"`
	Timeout        time.Duration        `json:"timeout"`
	Retries        int                  `json:"retries"`
	CircuitBreaker CircuitBreakerConfig `json:"circuit_breaker"`
	Authentication AuthConfig           `json:"authentication"`
}

// CircuitBreakerConfig holds circuit breaker settings
type CircuitBreakerConfig struct {
	FailureThreshold int           `json:"failure_threshold"`
	ResetTimeout     time.Duration `json:"reset_timeout"`
	MonitoringWindow time.Duration `json:"monitoring_window"`
}

// AuthConfig holds authentication settings
type AuthConfig struct {
	Type                 string            `json:"type"`
	Credentials          map[string]string `json:"credentials"`
	TokenRefreshInterval time.Duration     `json:"token_refresh_interval"`
}

// Client interface for making requests
type Client interface {
	VerifyTrace(ctx context.Context, trace *Trace) (*VerificationResult, error)
}

// NewSDK creates a new SDK instance
func NewSDK(config Config, client Client) *SDK {
	if config.Timeout == 0 {
		config.Timeout = 30 * time.Second
	}
	if config.Retries == 0 {
		config.Retries = 3
	}
	if config.CircuitBreaker.FailureThreshold == 0 {
		config.CircuitBreaker.FailureThreshold = 5
	}
	if config.CircuitBreaker.ResetTimeout == 0 {
		config.CircuitBreaker.ResetTimeout = 60 * time.Second
	}

	return &SDK{
		client: client,
		config: config,
	}
}

// VerifyTrace verifies a trace with the Policy Kernel
func (s *SDK) VerifyTrace(ctx context.Context, trace *Trace) (*VerificationResult, error) {
	ctx, cancel := context.WithTimeout(ctx, s.config.Timeout)
	defer cancel()

	result, err := s.client.VerifyTrace(ctx, trace)
	if err != nil {
		return nil, fmt.Errorf("trace verification failed: %w", err)
	}

	return result, nil
}

// GetVersion returns the SDK version
func (s *SDK) GetVersion() string {
	return "1.0.0"
}

// GetConfig returns the current SDK configuration
func (s *SDK) GetConfig() Config {
	return s.config
}
