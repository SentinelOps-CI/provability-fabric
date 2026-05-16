// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// VerifySignedBundleIntegrity recomputes digests and ensures verification still passes.
func VerifySignedBundleIntegrity(signed *SignedScienceClaimBundle) error {
	if signed == nil {
		return fmt.Errorf("signed bundle is nil")
	}
	if signed.SchemaVersion != SchemaSignedScienceClaim {
		return fmt.Errorf("unexpected schema_version %q", signed.SchemaVersion)
	}
	if !VerificationPassed(signed.VerificationResult) {
		return fmt.Errorf("embedded verification status is %s", signed.VerificationResult.Status)
	}

	expectedResultDigest := DigestVerificationResult(signed.VerificationResult)
	if signed.VerificationResult.SignatureOrDigest != expectedResultDigest {
		return fmt.Errorf("verification_result digest mismatch")
	}

	expectedWrapper := digestSignedBundle(signed)
	if signed.SignatureOrDigest != expectedWrapper {
		return fmt.Errorf("signed wrapper digest mismatch")
	}

	if signed.BundleDigest != "" && !strings.HasPrefix(signed.BundleDigest, "sha256:") {
		return fmt.Errorf("bundle_digest must be sha256-prefixed")
	}
	return nil
}
