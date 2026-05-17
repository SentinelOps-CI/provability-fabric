// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"os"
)

const signatureField = "signature_or_digest"

// CanonicalHash computes the PCS canonical digest for a JSON object (signature_or_digest stripped).
func CanonicalHash(data map[string]any) (string, error) {
	payload, err := CanonicalJSONBytes(data)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(payload)
	return "sha256:" + hexEncode(sum[:]), nil
}

// CanonicalHashFromBytes parses JSON bytes and returns the PCS canonical digest.
func CanonicalHashFromBytes(raw []byte) (string, error) {
	var doc map[string]any
	if err := json.Unmarshal(raw, &doc); err != nil {
		return "", fmt.Errorf("parse JSON for canonical hash: %w", err)
	}
	return CanonicalHash(doc)
}

// CanonicalHashFromFile reads a JSON artifact and returns its PCS canonical digest.
func CanonicalHashFromFile(path string) (string, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return "", err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return "", fmt.Errorf("read artifact: %w", err)
	}
	return CanonicalHashFromBytes(data)
}

// CanonicalJSONBytes returns compact canonical UTF-8 JSON for hashing (signature stripped).
func CanonicalJSONBytes(data map[string]any) ([]byte, error) {
	return CanonicalJSON(canonicalizeForHash(data))
}

func canonicalizeForHash(data map[string]any) map[string]any {
	out := make(map[string]any, len(data))
	for k, v := range data {
		if k == signatureField {
			continue
		}
		out[k] = v
	}
	return out
}

func hexEncode(b []byte) string {
	const hexdigits = "0123456789abcdef"
	out := make([]byte, len(b)*2)
	for i, v := range b {
		out[i*2] = hexdigits[v>>4]
		out[i*2+1] = hexdigits[v&0x0f]
	}
	return string(out)
}

// FileDigest returns sha256 of raw file bytes (release manifest / handoff input_artifacts pins).
func FileDigest(path string) (string, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return "", err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return "", fmt.Errorf("read file: %w", err)
	}
	sum := sha256.Sum256(data)
	return "sha256:" + hexEncode(sum[:]), nil
}
