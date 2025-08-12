package policykernel

import (
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"time"
)

// PFSignature represents a Policy Fast-Path Signature
type PFSignature struct {
	Signature  string    `json:"signature"`
	PublicKey  string    `json:"public_key"`
	ExpiresAt  time.Time `json:"expires_at"`
	CacheKey   CacheKey  `json:"cache_key"`
	CreatedAt  time.Time `json:"created_at"`
	PolicyHash string    `json:"policy_hash"`
}

// PFSignatureKeyPair represents a key pair for signing PF signatures
type PFSignatureKeyPair struct {
	PrivateKey ed25519.PrivateKey
	PublicKey  ed25519.PublicKey
}

// NewPFSignatureKeyPair generates a new Ed25519 key pair for PF signatures
func NewPFSignatureKeyPair() (*PFSignatureKeyPair, error) {
	publicKey, privateKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, fmt.Errorf("failed to generate Ed25519 key pair: %w", err)
	}

	return &PFSignatureKeyPair{
		PrivateKey: privateKey,
		PublicKey:  publicKey,
	}, nil
}

// SignDecision creates a PF signature for an approved decision
func (kp *PFSignatureKeyPair) SignDecision(cacheKey CacheKey, policyHash string, ttl time.Duration) (*PFSignature, error) {
	// Create the signature payload
	payload := PFSignaturePayload{
		CacheKey:   cacheKey,
		PolicyHash: policyHash,
		ExpiresAt:  time.Now().Add(ttl),
		CreatedAt:  time.Now(),
	}

	// Serialize the payload
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal signature payload: %w", err)
	}

	// Hash the payload
	payloadHash := sha256.Sum256(payloadBytes)

	// Sign the hash
	signature := ed25519.Sign(kp.PrivateKey, payloadHash[:])

	// Create the PF signature
	pfSig := &PFSignature{
		Signature:  base64.StdEncoding.EncodeToString(signature),
		PublicKey:  hex.EncodeToString(kp.PublicKey),
		ExpiresAt:  payload.ExpiresAt,
		CacheKey:   cacheKey,
		CreatedAt:  payload.CreatedAt,
		PolicyHash: policyHash,
	}

	return pfSig, nil
}

// VerifyPFSignature verifies a PF signature
func VerifyPFSignature(pfSig *PFSignature) (bool, error) {
	// Check if signature has expired
	if time.Now().After(pfSig.ExpiresAt) {
		return false, fmt.Errorf("PF signature has expired")
	}

	// Decode the public key
	publicKeyBytes, err := hex.DecodeString(pfSig.PublicKey)
	if err != nil {
		return false, fmt.Errorf("invalid public key format: %w", err)
	}

	// Decode the signature
	signatureBytes, err := base64.StdEncoding.DecodeString(pfSig.Signature)
	if err != nil {
		return false, fmt.Errorf("invalid signature format: %w", err)
	}

	// Recreate the payload for verification
	payload := PFSignaturePayload{
		CacheKey:   pfSig.CacheKey,
		PolicyHash: pfSig.PolicyHash,
		ExpiresAt:  pfSig.ExpiresAt,
		CreatedAt:  pfSig.CreatedAt,
	}

	// Serialize the payload
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return false, fmt.Errorf("failed to marshal signature payload: %w", err)
	}

	// Hash the payload
	payloadHash := sha256.Sum256(payloadBytes)

	// Verify the signature
	valid := ed25519.Verify(publicKeyBytes, payloadHash[:], signatureBytes)
	if !valid {
		return false, fmt.Errorf("invalid signature")
	}

	return true, nil
}

// PFSignaturePayload represents the data that gets signed
type PFSignaturePayload struct {
	CacheKey   CacheKey  `json:"cache_key"`
	PolicyHash string    `json:"policy_hash"`
	ExpiresAt  time.Time `json:"expires_at"`
	CreatedAt  time.Time `json:"created_at"`
}

// IsExpired checks if the PF signature has expired
func (pf *PFSignature) IsExpired() bool {
	return time.Now().After(pf.ExpiresAt)
}

// GetCacheKey returns the cache key from the signature
func (pf *PFSignature) GetCacheKey() CacheKey {
	return pf.CacheKey
}

// GetPolicyHash returns the policy hash from the signature
func (pf *PFSignature) GetPolicyHash() string {
	return pf.PolicyHash
}

// String returns a string representation of the PF signature
func (pf *PFSignature) String() string {
	data, _ := json.Marshal(pf)
	return base64.StdEncoding.EncodeToString(data)
}

// FromString creates a PF signature from a string representation
func PFSignatureFromString(s string) (*PFSignature, error) {
	data, err := base64.StdEncoding.DecodeString(s)
	if err != nil {
		return nil, fmt.Errorf("failed to decode signature string: %w", err)
	}

	var pfSig PFSignature
	if err := json.Unmarshal(data, &pfSig); err != nil {
		return nil, fmt.Errorf("failed to unmarshal signature: %w", err)
	}

	return &pfSig, nil
}

// ValidatePFSignature validates a PF signature and returns the cache key if valid
func ValidatePFSignature(signatureStr string) (*CacheKey, error) {
	// Parse the signature
	pfSig, err := PFSignatureFromString(signatureStr)
	if err != nil {
		return nil, fmt.Errorf("failed to parse PF signature: %w", err)
	}

	// Verify the signature
	valid, err := VerifyPFSignature(pfSig)
	if err != nil {
		return nil, fmt.Errorf("signature verification failed: %w", err)
	}

	if !valid {
		return nil, fmt.Errorf("invalid PF signature")
	}

	// Return the cache key for cache lookup
	return &pfSig.CacheKey, nil
}
