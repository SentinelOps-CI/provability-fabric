// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
)

// ProducerRepoPin is a pinned producer repository commit.
type ProducerRepoPin struct {
	Repo     string `json:"repo"`
	Commit   string `json:"commit"`
	LocalDev bool   `json:"local_dev,omitempty"`
}

// ManifestArtifactEntry describes a registered release artifact.
type ManifestArtifactEntry struct {
	ArtifactType  string `json:"artifact_type"`
	Schema        string `json:"schema"`
	Producer      string `json:"producer"`
	SourceRepo    string `json:"source_repo"`
	SourceCommit  string `json:"source_commit"`
	SHA256        string `json:"sha256"`
	LocalDev      bool   `json:"local_dev,omitempty"`
}

// ReleaseManifest is ReleaseManifest.v0 (artifact pins and producer commits for release-chain verify).
type ReleaseManifest struct {
	SchemaVersion     string                           `json:"schema_version"`
	ReleaseID         string                           `json:"release_id"`
	ReleaseCandidate  string                           `json:"release_candidate"`
	GeneratedAt       string                           `json:"generated_at"`
	ValidationProfile string                           `json:"validation_profile"`
	ProducerRepos     map[string]ProducerRepoPin       `json:"producer_repos"`
	Artifacts         map[string]ManifestArtifactEntry `json:"artifacts"`
	ReleaseStatus     string                           `json:"release_status"`
	SignatureOrDigest string                           `json:"signature_or_digest"`
}

// LoadReleaseManifest reads ReleaseManifest.v0 JSON from disk.
func LoadReleaseManifest(path string) (*ReleaseManifest, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read release manifest: %w", err)
	}
	var manifest ReleaseManifest
	if err := json.Unmarshal(data, &manifest); err != nil {
		return nil, fmt.Errorf("parse release manifest: %w", err)
	}
	return &manifest, nil
}

// ValidateReleaseManifestFile validates manifest JSON against pcs-core schema.
func ValidateReleaseManifestFile(repoRoot, path string) error {
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
	if err := ValidateDocumentAgainstSchema(repoRoot, "ReleaseManifest.v0.schema.json", doc); err != nil {
		return err
	}
	var manifest ReleaseManifest
	if err := json.Unmarshal(data, &manifest); err != nil {
		return err
	}
	return ValidateReleaseManifestSemantics(&manifest)
}

func firstCertificate(bundle *ScienceClaimBundle) *TraceCertificate {
	for _, cert := range bundle.Certificates {
		if cert != nil {
			return cert
		}
	}
	return nil
}
