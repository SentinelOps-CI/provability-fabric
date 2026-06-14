// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"
)

// ArtifactRef is a digest-bound reference to a bundled artifact.
type ArtifactRef struct {
	Role      string `json:"role"`
	Path      string `json:"path"`
	MediaType string `json:"media_type"`
	Digest    string `json:"digest"`
}

// ReplayContext describes executable replay inputs for v0.2 bundles.
type ReplayContext struct {
	KitTracePath   string `json:"kit_trace_path,omitempty"`
	FixturesPath   string `json:"fixtures_path,omitempty"`
	LowViewOracle  bool   `json:"low_view_oracle,omitempty"`
}

// EvidenceBundle is the v0.1/v0.2 bundle manifest.
type EvidenceBundle struct {
	BundleID      string         `json:"bundle_id"`
	SchemaVersion string         `json:"schema_version"`
	CreatedAt     string         `json:"created_at"`
	Producer      string         `json:"producer"`
	Artifacts     []ArtifactRef  `json:"artifacts"`
	ReplayContext *ReplayContext `json:"replay_context,omitempty"`
	BundleDigest  string         `json:"bundle_digest"`
}

// PackManifest describes inputs for bundle pack.
type PackManifest struct {
	SchemaVersion string `json:"schema_version"`
	BundleID      string `json:"bundle_id"`
	Producer      string `json:"producer"`
	CreatedAt     string `json:"created_at,omitempty"`
	ReplayContext *ReplayContext `json:"replay_context,omitempty"`
	Artifacts     []struct {
		Role      string `json:"role"`
		Path      string `json:"path"`
		MediaType string `json:"media_type,omitempty"`
	} `json:"artifacts"`
}

var roleMediaTypes = map[string]string{
	"claim":           "application/vnd.provability-fabric.evidence.claim+json",
	"proof":           "application/vnd.provability-fabric.evidence.proof+json",
	"attestation":     "application/vnd.provability-fabric.evidence.attestation+json",
	"execution-trace": "application/vnd.provability-fabric.evidence.execution-trace+json",
	"cert-v1":         "application/vnd.cert-v1+json",
}

// PackOptions controls bundle pack behavior.
type PackOptions struct {
	ManifestPath string
	OutPath      string
	BaseDir      string
}

// Pack reads a manifest, resolves artifact digests, and writes a bundle JSON file.
func Pack(opts PackOptions) (*EvidenceBundle, error) {
	if opts.BaseDir == "" {
		opts.BaseDir = filepath.Dir(opts.ManifestPath)
	}
	data, err := os.ReadFile(opts.ManifestPath)
	if err != nil {
		return nil, fmt.Errorf("read manifest: %w", err)
	}
	var manifest PackManifest
	if err := json.Unmarshal(data, &manifest); err != nil {
		return nil, fmt.Errorf("parse manifest: %w", err)
	}
	if manifest.SchemaVersion != SchemaVersion && manifest.SchemaVersion != SchemaVersionV02 {
		return nil, fmt.Errorf("unsupported schema_version %q", manifest.SchemaVersion)
	}
	if manifest.BundleID == "" {
		return nil, fmt.Errorf("manifest missing bundle_id")
	}
	if manifest.Producer == "" {
		manifest.Producer = "pf-evidence/v0.1"
	}
	if manifest.CreatedAt == "" {
		manifest.CreatedAt = time.Now().UTC().Format(time.RFC3339)
	}
	if len(manifest.Artifacts) == 0 {
		return nil, fmt.Errorf("manifest missing artifacts")
	}

	refs := make([]ArtifactRef, 0, len(manifest.Artifacts))
	for _, art := range manifest.Artifacts {
		if art.Role == "" || art.Path == "" {
			return nil, fmt.Errorf("artifact missing role or path")
		}
		mediaType := art.MediaType
		if mediaType == "" {
			mediaType = roleMediaTypes[art.Role]
			if mediaType == "" {
				return nil, fmt.Errorf("unknown role %q and no media_type provided", art.Role)
			}
		}
		absPath := filepath.Join(opts.BaseDir, filepath.FromSlash(art.Path))
		digest, err := FileDigest(absPath)
		if err != nil {
			return nil, fmt.Errorf("digest artifact %s: %w", art.Path, err)
		}
		refs = append(refs, ArtifactRef{
			Role:      art.Role,
			Path:      filepath.ToSlash(art.Path),
			MediaType: mediaType,
			Digest:    digest,
		})
	}

	bundle := EvidenceBundle{
		BundleID:      manifest.BundleID,
		SchemaVersion: manifest.SchemaVersion,
		CreatedAt:     manifest.CreatedAt,
		Producer:      manifest.Producer,
		ReplayContext: manifest.ReplayContext,
		Artifacts:     refs,
	}
	digest, err := bundleDigest(bundle)
	if err != nil {
		return nil, err
	}
	bundle.BundleDigest = digest

	out, err := json.MarshalIndent(bundle, "", "  ")
	if err != nil {
		return nil, err
	}
	out = append(out, '\n')
	if err := os.WriteFile(opts.OutPath, out, 0644); err != nil {
		return nil, fmt.Errorf("write bundle: %w", err)
	}
	return &bundle, nil
}

func bundleDigest(bundle EvidenceBundle) (string, error) {
	m, err := bundleToMap(bundle)
	if err != nil {
		return "", err
	}
	delete(m, "bundle_digest")
	return CanonicalJSONDigest(m, "")
}

// bundleToMap converts a bundle struct to map[string]any via JSON round-trip
// so nested artifact slices hash consistently with fixture tooling.
func bundleToMap(bundle EvidenceBundle) (map[string]any, error) {
	data, err := json.Marshal(bundle)
	if err != nil {
		return nil, err
	}
	var out map[string]any
	if err := json.Unmarshal(data, &out); err != nil {
		return nil, err
	}
	return out, nil
}
