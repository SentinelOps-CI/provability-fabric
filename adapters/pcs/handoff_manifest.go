// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

const (
	ComponentLabTrustGym        = "LabTrust-Gym"
	ComponentProvabilityFabric  = "Provability Fabric"
	HandoffStatusValidated      = "Validated"
	certifiedBundleInvariantKey   = "certified_bundle_hash"
	certificateIDInvariantKey     = "certificate_id"
	traceHashInvariantKey         = "trace_hash"
	defaultCertifiedBundleName    = "science_claim_bundle.certified.json"
)

// HandoffArtifactRef is a pcs-core handoff_artifact_ref.
type HandoffArtifactRef struct {
	ArtifactType string `json:"artifact_type"`
	SHA256       string `json:"sha256,omitempty"`
}

// HandoffManifest is HandoffManifest.v0 from pcs-core.
type HandoffManifest struct {
	SchemaVersion     string                        `json:"schema_version"`
	HandoffID         string                        `json:"handoff_id"`
	HandoffKind       string                        `json:"handoff_kind"`
	FromComponent     string                        `json:"from_component"`
	ToComponent       string                        `json:"to_component"`
	CreatedAt         string                        `json:"created_at"`
	SourceRepo        string                        `json:"source_repo"`
	SourceCommit      string                        `json:"source_commit"`
	InputArtifacts    map[string]HandoffArtifactRef `json:"input_artifacts"`
	ExpectedOutputs   map[string]HandoffArtifactRef `json:"expected_outputs"`
	Invariants        map[string]string             `json:"invariants"`
	Status            string                        `json:"status"`
	SignatureOrDigest string                        `json:"signature_or_digest"`
}

// LoadedHandoff is either HandoffManifest.v0 or legacy pf_handoff.json.
type LoadedHandoff struct {
	Manifest *HandoffManifest
	Legacy   *PFHandoff
}

// LoadHandoff reads pf_handoff.json or HandoffManifest.v0 JSON.
func LoadHandoff(path string) (*LoadedHandoff, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read handoff: %w", err)
	}
	var probe map[string]json.RawMessage
	if err := json.Unmarshal(data, &probe); err != nil {
		return nil, fmt.Errorf("parse handoff: %w", err)
	}
	if _, ok := probe["handoff_id"]; ok {
		var manifest HandoffManifest
		if err := json.Unmarshal(data, &manifest); err != nil {
			return nil, fmt.Errorf("parse handoff manifest: %w", err)
		}
		if err := manifest.validate(); err != nil {
			return nil, err
		}
		return &LoadedHandoff{Manifest: &manifest}, nil
	}
	legacy, err := LoadPFHandoff(path)
	if err != nil {
		return nil, err
	}
	return &LoadedHandoff{Legacy: legacy}, nil
}

func (h *HandoffManifest) validate() error {
	if h == nil {
		return fmt.Errorf("handoff manifest is nil")
	}
	if strings.TrimSpace(h.FromComponent) == "" {
		return fmt.Errorf("handoff from_component is required")
	}
	if strings.TrimSpace(h.ToComponent) == "" {
		return fmt.Errorf("handoff to_component is required")
	}
	if strings.TrimSpace(h.Status) == "" {
		return fmt.Errorf("handoff status is required")
	}
	return nil
}

// AssertBundleMatchesHandoff applies legacy or HandoffManifest.v0 guards.
func (loaded *LoadedHandoff) AssertBundleMatchesHandoff(bundle *ScienceClaimBundle, bundlePath string) error {
	if loaded == nil {
		return fmt.Errorf("handoff is required")
	}
	if loaded.Legacy != nil {
		return AssertBundleMatchesHandoff(bundle, bundlePath, loaded.Legacy)
	}
	return AssertBundleMatchesHandoffManifest(bundle, bundlePath, loaded.Manifest)
}

// AssertBundleMatchesHandoffManifest enforces HandoffManifest.v0 admission rules for PF verify.
func AssertBundleMatchesHandoffManifest(bundle *ScienceClaimBundle, bundlePath string, handoff *HandoffManifest) error {
	if handoff == nil {
		return fmt.Errorf("handoff manifest is required")
	}
	if err := handoff.validate(); err != nil {
		return err
	}
	if handoff.FromComponent != ComponentLabTrustGym {
		return fmt.Errorf("handoff from_component must be %q (got %q)", ComponentLabTrustGym, handoff.FromComponent)
	}
	if handoff.ToComponent != ComponentProvabilityFabric {
		return fmt.Errorf("handoff to_component must be %q (got %q)", ComponentProvabilityFabric, handoff.ToComponent)
	}
	if handoff.Status != HandoffStatusValidated {
		return fmt.Errorf("handoff status must be %q (got %q)", HandoffStatusValidated, handoff.Status)
	}
	if err := ValidateHandoffManifestSemantics(handoff); err != nil {
		return err
	}

	bundleHash, err := bundleContentDigest(bundle, bundlePath)
	if err != nil {
		return err
	}
	certID, traceHash, err := primaryCertAndTrace(bundle)
	if err != nil {
		return err
	}

	if want := strings.TrimSpace(handoff.Invariants[certifiedBundleInvariantKey]); want != "" && bundleHash != want {
		return fmt.Errorf("handoff certified_bundle_hash mismatch: bundle %s handoff %s", bundleHash, want)
	}
	if want := strings.TrimSpace(handoff.Invariants[certificateIDInvariantKey]); want != "" && certID != want {
		return fmt.Errorf("handoff certificate_id mismatch: bundle %q handoff %q", certID, want)
	}
	if want := strings.TrimSpace(handoff.Invariants[traceHashInvariantKey]); want != "" && traceHash != want {
		return fmt.Errorf("handoff trace_hash mismatch: bundle %s handoff %s", traceHash, want)
	}

	bundleName := certifiedBundleFileName(bundlePath)
	ref, ok := handoff.InputArtifacts[bundleName]
	if !ok {
		for name, r := range handoff.InputArtifacts {
			if r.ArtifactType == "ScienceClaimBundle.v0" {
				ref, bundleName = r, name
				ok = true
				break
			}
		}
	}
	if !ok {
		return fmt.Errorf("handoff input_artifacts missing certified science claim bundle")
	}
	if ref.ArtifactType != "" && ref.ArtifactType != "ScienceClaimBundle.v0" {
		return fmt.Errorf("handoff input_artifacts[%s] artifact_type must be ScienceClaimBundle.v0", bundleName)
	}
	if want := strings.TrimSpace(ref.SHA256); want != "" && bundleHash != want {
		return fmt.Errorf("handoff input_artifacts[%s] sha256 mismatch: bundle %s handoff %s", bundleName, bundleHash, want)
	}
	return nil
}

func certifiedBundleFileName(bundlePath string) string {
	if strings.TrimSpace(bundlePath) == "" {
		return defaultCertifiedBundleName
	}
	return filepathBase(bundlePath)
}

func filepathBase(path string) string {
	path = strings.ReplaceAll(path, "\\", "/")
	if i := strings.LastIndex(path, "/"); i >= 0 {
		return path[i+1:]
	}
	return path
}

// bundleContentDigest returns the handoff pin for a certified bundle file (raw file sha256).
func bundleContentDigest(bundle *ScienceClaimBundle, bundlePath string) (string, error) {
	if strings.TrimSpace(bundlePath) != "" {
		return FileDigest(bundlePath)
	}
	raw, err := json.Marshal(bundle)
	if err != nil {
		return "", err
	}
	return "sha256:" + SHA256Hex(raw), nil
}
