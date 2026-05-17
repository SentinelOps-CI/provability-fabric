// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
)

// CloneScienceClaimBundle returns a deep copy of bundle.
func CloneScienceClaimBundle(bundle *ScienceClaimBundle) (*ScienceClaimBundle, error) {
	if bundle == nil {
		return nil, nil
	}
	data, err := json.Marshal(bundle)
	if err != nil {
		return nil, err
	}
	var copy ScienceClaimBundle
	if err := json.Unmarshal(data, &copy); err != nil {
		return nil, err
	}
	return &copy, nil
}

// AssertBundlesCanonicallyEqual compares canonical JSON digests of two bundles.
func AssertBundlesCanonicallyEqual(a, b *ScienceClaimBundle) error {
	if a == nil || b == nil {
		return fmt.Errorf("cannot compare nil bundles")
	}
	ha, err := BundleCanonicalDigest(a)
	if err != nil {
		return err
	}
	hb, err := BundleCanonicalDigest(b)
	if err != nil {
		return err
	}
	if ha != hb {
		return fmt.Errorf("canonical bundle hash mismatch: %s vs %s", ha, hb)
	}
	return nil
}

// BundleCanonicalDigest returns sha256 digest of canonical bundle JSON.
func BundleCanonicalDigest(bundle *ScienceClaimBundle) (string, error) {
	payload, err := CanonicalJSON(bundle)
	if err != nil {
		return "", err
	}
	return "sha256:" + SHA256Hex(payload), nil
}
