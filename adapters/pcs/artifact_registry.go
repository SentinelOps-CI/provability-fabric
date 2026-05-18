// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// RegistryEntry is one ArtifactRegistry.v0 entries map value.
type RegistryEntry struct {
	ArtifactType          string   `json:"artifact_type"`
	Schema                string   `json:"schema"`
	Producer              string   `json:"producer"`
	AllowedStatuses       []string `json:"allowed_statuses"`
	RequiredReleaseFields []string `json:"required_release_fields"`
	SemanticChecks        []string `json:"semantic_checks"`
}

// ArtifactRegistry is ArtifactRegistry.v0 from pcs-core.
type ArtifactRegistry struct {
	SchemaVersion     string                   `json:"schema_version"`
	RegistryID        string                   `json:"registry_id"`
	RegistryVersion   string                   `json:"registry_version"`
	Entries           map[string]RegistryEntry `json:"entries"`
	SignatureOrDigest string                   `json:"signature_or_digest"`
}

// LoadArtifactRegistry reads ArtifactRegistry.v0 JSON (rejects ReleaseManifest.v0).
func LoadArtifactRegistry(path string) (*ArtifactRegistry, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read artifact registry: %w", err)
	}
	var probe map[string]json.RawMessage
	if err := json.Unmarshal(data, &probe); err != nil {
		return nil, fmt.Errorf("parse artifact registry: %w", err)
	}
	if _, ok := probe["release_id"]; ok {
		return nil, fmt.Errorf("%s is ReleaseManifest.v0; use --manifest for release-chain verify, not --registry", filepath.Base(resolved))
	}
	if _, ok := probe["registry_id"]; !ok {
		return nil, fmt.Errorf("%s is not ArtifactRegistry.v0 (missing registry_id)", filepath.Base(resolved))
	}
	var registry ArtifactRegistry
	if err := json.Unmarshal(data, &registry); err != nil {
		return nil, fmt.Errorf("parse artifact registry: %w", err)
	}
	return &registry, nil
}

// ValidateArtifactRegistryFile validates registry JSON against pcs-core schema.
func ValidateArtifactRegistryFile(repoRoot, path string) error {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	if err := ValidateDocumentAgainstSchema(repoRoot, "ArtifactRegistry.v0.schema.json", doc); err != nil {
		return err
	}
	var registry ArtifactRegistry
	if err := json.Unmarshal(data, &registry); err != nil {
		return err
	}
	return ValidateArtifactRegistrySemantics(&registry)
}

// ValidateArtifactRegistrySemantics enforces registry invariants for release mode.
func ValidateArtifactRegistrySemantics(registry *ArtifactRegistry) error {
	if registry == nil {
		return fmt.Errorf("artifact registry is nil")
	}
	if strings.TrimSpace(registry.RegistryID) == "" {
		return fmt.Errorf("registry_id is required")
	}
	if len(registry.Entries) == 0 {
		return fmt.Errorf("entries must not be empty")
	}
	return nil
}

func (r *ArtifactRegistry) entryByArtifactType(artifactType string) (RegistryEntry, bool) {
	if r == nil {
		return RegistryEntry{}, false
	}
	for _, entry := range r.Entries {
		if entry.ArtifactType == artifactType {
			return entry, true
		}
	}
	return RegistryEntry{}, false
}

// DefaultArtifactRegistryPath returns pcs-core/examples/artifact_registry.valid.json when present.
func DefaultArtifactRegistryPath() (string, bool) {
	for _, base := range pcsCoreSearchRoots() {
		candidate := filepath.Join(base, "examples", "artifact_registry.valid.json")
		if st, err := os.Stat(candidate); err == nil && !st.IsDir() {
			return candidate, true
		}
	}
	return "", false
}

func pcsCoreSearchRoots() []string {
	if _, ok := os.LookupEnv("PCS_CORE_PATH"); ok {
		if p := strings.TrimSpace(os.Getenv("PCS_CORE_PATH")); p != "" {
			return []string{p}
		}
		return nil
	}
	var roots []string
	if wd, err := os.Getwd(); err == nil {
		if root, err := FindRepoRoot(wd); err == nil {
			roots = append(roots, filepath.Join(root, "..", "pcs-core"))
		}
	}
	return roots
}
