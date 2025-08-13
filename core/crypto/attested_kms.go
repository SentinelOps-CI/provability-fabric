// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package crypto

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"time"
)

// AttestationResult represents the result of enclave attestation verification
type AttestationResult struct {
	Valid        bool                   `json:"valid"`
	EnclaveID   string                 `json:"enclave_id,omitempty"`
	Measurements map[string]string     `json:"measurements,omitempty"`
	ExpiresAt    time.Time             `json:"expires_at,omitempty"`
	Reason       string                `json:"reason,omitempty"`
	Details      string                `json:"details,omitempty"`
}

// KMSConfig holds configuration for KMS operations
type KMSConfig struct {
	Region             string        `json:"region"`
	KeyID              string        `json:"key_id"`
	TokenTTL           time.Duration `json:"token_ttl"`
	MaxOperations      int           `json:"max_operations"`
	RequireAttestation bool          `json:"require_attestation"`
}

// MockKMSClient represents a mock KMS client for testing
type MockKMSClient struct {
	encryptFunc func(plaintext []byte, context map[string]string) ([]byte, error)
	decryptFunc func(ciphertext []byte, context map[string]string) ([]byte, error)
}

// AttestedKMS provides KMS operations with enclave attestation requirements
type AttestedKMS struct {
	client   *MockKMSClient
	config   KMSConfig
	verifier AttestationVerifier
}

// AttestationVerifier interface for verifying enclave attestations
type AttestationVerifier interface {
	VerifyAttestation(ctx context.Context, attestationData []byte) (*AttestationResult, error)
}

// KMSOperation represents a KMS operation with attestation
type KMSOperation struct {
	OperationID   string             `json:"operation_id"`
	OperationType string             `json:"operation_type"`
	KeyID         string             `json:"key_id"`
	Attestation   *AttestationResult `json:"attestation"`
	Timestamp     time.Time          `json:"timestamp"`
	ExpiresAt     time.Time          `json:"expires_at"`
}

// NewAttestedKMS creates a new AttestedKMS instance
func NewAttestedKMS(client *MockKMSClient, config KMSConfig, verifier AttestationVerifier) *AttestedKMS {
	if config.TokenTTL == 0 {
		config.TokenTTL = 1 * time.Hour
	}
	if config.MaxOperations == 0 {
		config.MaxOperations = 1000
	}

	return &AttestedKMS{
		client:   client,
		config:   config,
		verifier: verifier,
	}
}

// GenerateAttestedToken creates a short-lived token for KMS access
func (ak *AttestedKMS) GenerateAttestedToken(ctx context.Context, attestationData []byte) (string, error) {
	if !ak.config.RequireAttestation {
		return "", fmt.Errorf("attestation required but not configured")
	}

	// Verify attestation
	attestation, err := ak.verifier.VerifyAttestation(ctx, attestationData)
	if err != nil {
		return "", fmt.Errorf("attestation verification failed: %w", err)
	}

	if !attestation.Valid {
		return "", fmt.Errorf("invalid attestation: %s", attestation.Reason)
	}

	// Check if attestation is expired
	if time.Now().After(attestation.ExpiresAt) {
		return "", fmt.Errorf("attestation expired at %v", attestation.ExpiresAt)
	}

	// Generate token with attestation claims
	tokenData := map[string]interface{}{
		"enclave_id":  attestation.EnclaveID,
		"key_id":      ak.config.KeyID,
		"exp":         time.Now().Add(ak.config.TokenTTL).Unix(),
		"iat":         time.Now().Unix(),
		"jti":         fmt.Sprintf("token-%d", time.Now().UnixNano()),
		"measurements": attestation.Measurements,
	}

	// In production, this would be a proper JWT with cryptographic signature
	tokenBytes, err := json.Marshal(tokenData)
	if err != nil {
		return "", fmt.Errorf("failed to marshal token: %w", err)
	}

	return base64.URLEncoding.EncodeToString(tokenBytes), nil
}

// EncryptWithAttestation encrypts data using KMS with attestation verification
func (ak *AttestedKMS) EncryptWithAttestation(ctx context.Context, plaintext []byte, attestationData []byte) ([]byte, error) {
	if !ak.config.RequireAttestation {
		if ak.client.encryptFunc != nil {
			return ak.client.encryptFunc(plaintext, nil)
		}
		return plaintext, nil // Mock encryption
	}

	// Verify attestation
	attestation, err := ak.verifier.VerifyAttestation(ctx, attestationData)
	if err != nil {
		return nil, fmt.Errorf("attestation verification failed: %w", err)
	}

	if !attestation.Valid {
		return nil, fmt.Errorf("invalid attestation: %s", attestation.Reason)
	}

	// Check if attestation is expired
	if time.Now().After(attestation.ExpiresAt) {
		return nil, fmt.Errorf("attestation expired at %v", attestation.ExpiresAt)
	}

	// Add attestation context to encryption
	context := map[string]string{
		"enclave_id":  attestation.EnclaveID,
		"attested_at": attestation.ExpiresAt.Format(time.RFC3339),
	}

	// Encrypt with attestation context
	if ak.client.encryptFunc != nil {
		return ak.client.encryptFunc(plaintext, context)
	}
	
	// Mock encryption with context
	contextBytes, _ := json.Marshal(context)
	encrypted := append(plaintext, contextBytes...)
	return encrypted, nil
}

// DecryptWithAttestation decrypts data using KMS with attestation verification
func (ak *AttestedKMS) DecryptWithAttestation(ctx context.Context, ciphertext []byte, attestationData []byte) ([]byte, error) {
	if !ak.config.RequireAttestation {
		if ak.client.decryptFunc != nil {
			return ak.client.decryptFunc(ciphertext, nil)
		}
		return ciphertext, nil // Mock decryption
	}

	// Verify attestation
	attestation, err := ak.verifier.VerifyAttestation(ctx, attestationData)
	if err != nil {
		return nil, fmt.Errorf("attestation verification failed: %w", err)
	}

	if !attestation.Valid {
		return nil, fmt.Errorf("invalid attestation: %s", attestation.Reason)
	}

	// Check if attestation is expired
	if time.Now().After(attestation.ExpiresAt) {
		return nil, fmt.Errorf("attestation expired at %v", attestation.ExpiresAt)
	}

	// Add attestation context to decryption
	context := map[string]string{
		"enclave_id":  attestation.EnclaveID,
		"attested_at": attestation.ExpiresAt.Format(time.RFC3339),
	}

	// Decrypt with attestation context
	if ak.client.decryptFunc != nil {
		return ak.client.decryptFunc(ciphertext, context)
	}
	
	// Mock decryption - remove context bytes
	if len(ciphertext) > 0 {
		return ciphertext[:len(ciphertext)-len(context)], nil
	}
	return ciphertext, nil
}

// GenerateDataKeyWithAttestation generates a data key with attestation verification
func (ak *AttestedKMS) GenerateDataKeyWithAttestation(ctx context.Context, attestationData []byte) ([]byte, error) {
	if !ak.config.RequireAttestation {
		// Generate a mock 32-byte AES key
		key := make([]byte, 32)
		for i := range key {
			key[i] = byte(i % 256)
		}
		return key, nil
	}

	// Verify attestation
	attestation, err := ak.verifier.VerifyAttestation(ctx, attestationData)
	if err != nil {
		return nil, fmt.Errorf("attestation verification failed: %w", err)
	}

	if !attestation.Valid {
		return nil, fmt.Errorf("invalid attestation: %s", attestation.Reason)
	}

	// Check if attestation is expired
	if time.Now().After(attestation.ExpiresAt) {
		return nil, fmt.Errorf("attestation expired at %v", attestation.ExpiresAt)
	}

	// Add attestation context to key generation
	context := map[string]string{
		"enclave_id":  attestation.EnclaveID,
		"attested_at": attestation.ExpiresAt.Format(time.RFC3339),
	}

	// Generate a mock 32-byte AES key with context
	key := make([]byte, 32)
	for i := range key {
		key[i] = byte(i % 256)
	}
	
	// Add context to key (in production, this would be proper KMS integration)
	contextBytes, _ := json.Marshal(context)
	keyWithContext := append(key, contextBytes...)
	
	return keyWithContext, nil
}

// VerifyKeyPolicy checks if the KMS key policy allows attested enclave access
func (ak *AttestedKMS) VerifyKeyPolicy(ctx context.Context) error {
	if !ak.config.RequireAttestation {
		return nil // No attestation required
	}

	// Mock key policy verification
	// In production, this would call KMS GetKeyPolicy and verify IAM conditions
	mockPolicy := map[string]interface{}{
		"Version": "2012-10-17",
		"Statement": []map[string]interface{}{
			{
				"Effect": "Allow",
				"Action": "kms:*",
				"Resource": "*",
				"Condition": map[string]interface{}{
					"StringEquals": map[string]interface{}{
						"kms:RecipientAttestation:ImageSha384": "mock-sha384-hash",
					},
				},
			},
		},
	}

	// Check if policy has attestation conditions
	hasAttestationConditions := ak.checkAttestationConditions(mockPolicy)
	if !hasAttestationConditions {
		return fmt.Errorf("key policy does not have required attestation conditions")
	}

	return nil
}

// checkAttestationConditions verifies that the key policy has attestation requirements
func (ak *AttestedKMS) checkAttestationConditions(policy map[string]interface{}) bool {
	// This is a simplified check - in production, you would parse the IAM policy
	// and verify specific conditions like kms:RecipientAttestation:ImageSha384
	
	policyStr, _ := json.Marshal(policy)
	policyString := string(policyStr)
	
	// Check for common attestation-related conditions
	attestationKeywords := []string{
		"kms:RecipientAttestation",
		"kms:ViaService",
		"kms:CallerAccount",
		"kms:EncryptionContext",
	}
	
	for _, keyword := range attestationKeywords {
		if contains(policyString, keyword) {
			return true
		}
	}
	
	return false
}

// contains checks if a string contains a substring
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || 
		(len(s) > len(substr) && (s[:len(substr)] == substr || 
		s[len(s)-len(substr):] == substr || 
		containsSubstring(s, substr))))
}

// containsSubstring checks if a string contains a substring (simplified)
func containsSubstring(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}

// GetAttestationMetrics returns metrics about attestation usage
func (ak *AttestedKMS) GetAttestationMetrics(ctx context.Context) (map[string]interface{}, error) {
	metrics := map[string]interface{}{
		"attestation_required": ak.config.RequireAttestation,
		"key_id":               ak.config.KeyID,
		"region":               ak.config.Region,
		"token_ttl":            ak.config.TokenTTL.String(),
		"max_operations":       ak.config.MaxOperations,
		"timestamp":            time.Now().Format(time.RFC3339),
	}

	return metrics, nil
}

// MockAttestationVerifier for testing
type MockAttestationVerifier struct {
	shouldSucceed bool
	attestation   *AttestationResult
}

// NewMockAttestationVerifier creates a mock verifier for testing
func NewMockAttestationVerifier(shouldSucceed bool) *MockAttestationVerifier {
	if shouldSucceed {
		return &MockAttestationVerifier{
			shouldSucceed: true,
			attestation: &AttestationResult{
				Valid:       true,
				EnclaveID:   "test-enclave-123",
				ExpiresAt:   time.Now().Add(1 * time.Hour),
				Measurements: map[string]string{"pcr0": "test-value"},
			},
		}
	}

	return &MockAttestationVerifier{
		shouldSucceed: false,
		attestation: &AttestationResult{
			Valid:  false,
			Reason: "mock failure",
		},
	}
}

// VerifyAttestation implements AttestationVerifier for testing
func (m *MockAttestationVerifier) VerifyAttestation(ctx context.Context, attestationData []byte) (*AttestationResult, error) {
	if !m.shouldSucceed {
		return m.attestation, nil
	}
	return m.attestation, nil
}
