// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"strings"
	"time"

	"github.com/google/uuid"
)

// SignVerificationResult builds SignedScienceClaimBundle.v0 for Scientific Memory import.
func SignVerificationResult(repoRoot string, bundle *ScienceClaimBundle, result VerificationResult) (*SignedScienceClaimBundle, error) {
	if !VerificationPassed(result) {
		return nil, fmt.Errorf("signing refused: verification status is %s", result.Status)
	}
	signed := &SignedScienceClaimBundle{
		SchemaVersion:      SchemaVersionV0,
		SignedBundleID:     fmt.Sprintf("signed-%s", uuid.NewString()),
		ScienceClaimBundle: bundle,
		VerificationResult: result,
		Signer:             VerifierName,
		SignedAt:           time.Now().UTC().Format(time.RFC3339),
		SourceRepo:         VerifierSourceRepo,
		SourceCommit:       ResolveSourceCommit(),
	}
	signed.SignatureOrDigest = digestSignedBundle(signed)
	if err := VerifySignedBundleIntegrity(signed); err != nil {
		return nil, err
	}
	if repoRoot != "" {
		if err := ValidateSignedScienceClaimBundle(repoRoot, signed); err != nil {
			return nil, fmt.Errorf("signed bundle schema: %w", err)
		}
	}
	return signed, nil
}

func digestSignedBundle(signed *SignedScienceClaimBundle) string {
	copy := *signed
	copy.SignatureOrDigest = ""
	payload, err := CanonicalJSON(copy)
	if err != nil {
		return ""
	}
	return "sha256:" + SHA256Hex(payload)
}

// VerifySignedBundleIntegrity recomputes digests and ensures verification still passes.
func VerifySignedBundleIntegrity(signed *SignedScienceClaimBundle) error {
	if signed == nil {
		return fmt.Errorf("signed bundle is nil")
	}
	if signed.SchemaVersion != SchemaVersionV0 {
		return fmt.Errorf("unexpected schema_version %q", signed.SchemaVersion)
	}
	if signed.ScienceClaimBundle == nil {
		return fmt.Errorf("science_claim_bundle is required")
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
	return nil
}

// FormatInspectSummary renders a human-readable inspection report with every check.
func FormatInspectSummary(signed *SignedScienceClaimBundle) string {
	var b strings.Builder
	vr := signed.VerificationResult
	fmt.Fprintf(&b, "Signed Science Claim Bundle\n")
	fmt.Fprintf(&b, "  signed_bundle_id:     %s\n", signed.SignedBundleID)
	fmt.Fprintf(&b, "  signer:               %s\n", signed.Signer)
	fmt.Fprintf(&b, "  signed_at:            %s\n", signed.SignedAt)
	fmt.Fprintf(&b, "  verification_id:      %s\n", vr.VerificationID)
	fmt.Fprintf(&b, "  bundle_id:            %s\n", vr.BundleID)
	fmt.Fprintf(&b, "  verification_status:  %s\n", vr.Status)
	fmt.Fprintf(&b, "  result_digest:        %s\n", vr.SignatureOrDigest)
	fmt.Fprintf(&b, "  wrapper_digest:       %s\n\n", signed.SignatureOrDigest)
	fmt.Fprintf(&b, "Checks (%d):\n", len(vr.Checks))
	for _, c := range vr.Checks {
		fmt.Fprintf(&b, "  [%s] %s\n", c.Status, c.CheckID)
		fmt.Fprintf(&b, "         %s\n", c.Description)
		detailsJSON, _ := json.Marshal(c.Details)
		fmt.Fprintf(&b, "         %s\n", string(detailsJSON))
	}
	return b.String()
}
