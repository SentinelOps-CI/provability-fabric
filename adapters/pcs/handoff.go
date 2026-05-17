// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

// PFHandoff is the LabTrust release handoff consumed by pf sign --handoff.
type PFHandoff struct {
	SchemaVersion       string `json:"schema_version"`
	CertifiedBundle     string `json:"certified_bundle,omitempty"`
	CertifiedBundleHash string `json:"certified_bundle_hash"`
	CertificateID       string `json:"certificate_id"`
	TraceHash           string `json:"trace_hash"`
}

// LoadPFHandoff reads pf_handoff.json from disk.
func LoadPFHandoff(path string) (*PFHandoff, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read handoff: %w", err)
	}
	var handoff PFHandoff
	if err := json.Unmarshal(data, &handoff); err != nil {
		return nil, fmt.Errorf("parse handoff: %w", err)
	}
	if err := handoff.validate(); err != nil {
		return nil, err
	}
	return &handoff, nil
}

func (h *PFHandoff) validate() error {
	if h == nil {
		return fmt.Errorf("handoff is nil")
	}
	if strings.TrimSpace(h.CertifiedBundleHash) == "" {
		return fmt.Errorf("handoff certified_bundle_hash is required")
	}
	if strings.TrimSpace(h.CertificateID) == "" {
		return fmt.Errorf("handoff certificate_id is required")
	}
	if strings.TrimSpace(h.TraceHash) == "" {
		return fmt.Errorf("handoff trace_hash is required")
	}
	return nil
}

// BuildPFHandoffFromBundle constructs a handoff document from the bundle under sign.
func BuildPFHandoffFromBundle(bundle *ScienceClaimBundle, bundlePath string) (*PFHandoff, error) {
	vi, err := BuildVerifiedInput(bundle, bundlePath)
	if err != nil {
		return nil, err
	}
	return &PFHandoff{
		SchemaVersion:       SchemaVersionV0,
		CertifiedBundle:     "science_claim_bundle.certified.json",
		CertifiedBundleHash: vi.BundleHash,
		CertificateID:       vi.CertificateID,
		TraceHash:           vi.TraceHash,
	}, nil
}

// AssertBundleMatchesHandoff ensures the certified bundle matches the LabTrust pf_handoff.json.
// certified_bundle_hash is compared to the on-disk certified JSON digest (same as verified_input.bundle_hash).
func AssertBundleMatchesHandoff(bundle *ScienceClaimBundle, bundlePath string, handoff *PFHandoff) error {
	if handoff == nil {
		return fmt.Errorf("handoff is required")
	}
	if err := handoff.validate(); err != nil {
		return err
	}
	bundleHash, err := bundleInputHash(bundle, bundlePath)
	if err != nil {
		return err
	}
	certID, traceHash, err := primaryCertAndTrace(bundle)
	if err != nil {
		return err
	}
	if bundleHash != handoff.CertifiedBundleHash {
		return fmt.Errorf("handoff certified_bundle_hash mismatch: bundle %s handoff %s",
			bundleHash, handoff.CertifiedBundleHash)
	}
	if certID != handoff.CertificateID {
		return fmt.Errorf("handoff certificate_id mismatch: bundle %q handoff %q",
			certID, handoff.CertificateID)
	}
	if traceHash != handoff.TraceHash {
		return fmt.Errorf("handoff trace_hash mismatch: bundle %s handoff %s",
			traceHash, handoff.TraceHash)
	}
	return nil
}
