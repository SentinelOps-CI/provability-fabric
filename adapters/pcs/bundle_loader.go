// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

// LoadScienceClaimBundle reads and unmarshals a ScienceClaimBundle.v0 JSON file.
func LoadScienceClaimBundle(path string) (*ScienceClaimBundle, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read bundle %s: %w", path, err)
	}
	var bundle ScienceClaimBundle
	if err := json.Unmarshal(data, &bundle); err != nil {
		return nil, fmt.Errorf("parse bundle JSON: %w", err)
	}
	return &bundle, nil
}

// LoadSignedScienceClaimBundle reads a signed wrapper produced by pf sign science-claim.
func LoadSignedScienceClaimBundle(path string) (*SignedScienceClaimBundle, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read signed bundle %s: %w", path, err)
	}
	var signed SignedScienceClaimBundle
	if err := json.Unmarshal(data, &signed); err != nil {
		return nil, fmt.Errorf("parse signed bundle JSON: %w", err)
	}
	return &signed, nil
}

// BundleDigest returns a stable sha256 digest for the raw bundle bytes.
func BundleDigest(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return SHA256Hex(data), nil
}

// ResolveSchemaPath locates a PCS schema under config/schemas/pcs from repo root.
func ResolveSchemaPath(repoRoot, schemaFile string) string {
	return filepath.Join(repoRoot, "config", "schemas", "pcs", schemaFile)
}

// FindRepoRoot walks upward from startDir until config/schemas/pcs is found.
func FindRepoRoot(startDir string) (string, error) {
	dir, err := filepath.Abs(startDir)
	if err != nil {
		return "", err
	}
	for {
		candidate := filepath.Join(dir, "config", "schemas", "pcs")
		if st, err := os.Stat(candidate); err == nil && st.IsDir() {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}
	return "", fmt.Errorf("provability-fabric repo root not found from %s", startDir)
}
