// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"strings"
	"time"
)

// IntegrityOptions configures signed-bundle integrity verification.
type IntegrityOptions struct {
	// VerifyPFDigests recomputes PF canonical digests (required for pf sign output).
	// External signers (e.g. LabTrust) may use different digest rules; leave false for inspect.
	VerifyPFDigests bool
}

// SignVerificationResult builds SignedScienceClaimBundle.v0 for Scientific Memory import.
func SignVerificationResult(repoRoot string, bundle *ScienceClaimBundle, result VerificationResult) (*SignedScienceClaimBundle, error) {
	return SignVerificationResultWithOptions(repoRoot, bundle, result, SignOptions{})
}

// SignOptions configures signing provenance enforcement.
type SignOptions struct {
	ReleaseMode bool
	LocalDev    bool
	BundlePath  string
}

// SignVerificationResultWithOptions builds a signed wrapper with optional release-mode checks.
func SignVerificationResultWithOptions(repoRoot string, bundle *ScienceClaimBundle, result VerificationResult, opts SignOptions) (*SignedScienceClaimBundle, error) {
	if !VerificationPassed(result) {
		return nil, fmt.Errorf("signing refused: verification status is %s", result.Status)
	}
	wrapperCommit := strings.TrimSpace(result.SourceCommit)
	if wrapperCommit == "" {
		wrapperCommit = ResolveSourceCommit()
	}
	if err := ValidatePFProvenanceCommit(wrapperCommit, opts.ReleaseMode, opts.LocalDev); err != nil {
		return nil, err
	}
	var inputVI VerifiedInput
	if strings.TrimSpace(opts.BundlePath) != "" {
		computed, err := BuildVerifiedInput(bundle, opts.BundlePath)
		if err != nil {
			return nil, fmt.Errorf("pre-sign verified_input: %w", err)
		}
		if result.VerifiedInput != nil && !verifiedInputsEqual(*result.VerifiedInput, computed) {
			return nil, fmt.Errorf("verification_result.verified_input does not match bundle being signed")
		}
		inputVI = computed
	} else if result.VerifiedInput != nil {
		inputVI = *result.VerifiedInput
	} else {
		computed, err := BuildVerifiedInput(bundle, "")
		if err != nil {
			return nil, fmt.Errorf("pre-sign verified_input: %w", err)
		}
		inputVI = computed
	}
	if result.VerifiedInput == nil {
		result.VerifiedInput = &inputVI
		result.SignatureOrDigest = DigestVerificationResult(result)
	}
	embedded, err := CloneScienceClaimBundle(bundle)
	if err != nil {
		return nil, fmt.Errorf("clone bundle for signing: %w", err)
	}
	signedAt := time.Now().UTC().Format(time.RFC3339)
	if DeterministicMode() {
		signedAt = deterministicRFC3339(bundle)
	}
	signed := &SignedScienceClaimBundle{
		SchemaVersion:         SchemaVersionV0,
		SignedBundleID:        newSignedBundleID(bundle.BundleID, result.VerificationID),
		ScienceClaimBundle:    embedded,
		VerificationResult:    result,
		Signer:                VerifierName,
		SignedAt:              signedAt,
		SourceRepo:            VerifierSourceRepo,
		SourceCommit:          wrapperCommit,
		SignedInputBundleHash: result.VerifiedInput.BundleHash,
	}
	if err := AssertReleaseArtifactChain(bundle, result, signed); err != nil {
		return nil, fmt.Errorf("release artifact chain: %w", err)
	}
	signed.SignatureOrDigest = digestSignedBundle(signed)
	if err := VerifySignedBundleIntegrity(signed, IntegrityOptions{VerifyPFDigests: true}); err != nil {
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

// VerifySignedBundleIntegrity validates structure and optionally PF digest fields.
func VerifySignedBundleIntegrity(signed *SignedScienceClaimBundle, opts IntegrityOptions) error {
	if signed == nil {
		return fmt.Errorf("signed bundle is nil")
	}
	if signed.SchemaVersion != SchemaVersionV0 {
		return fmt.Errorf("unexpected schema_version %q (want %q)", signed.SchemaVersion, SchemaVersionV0)
	}
	if signed.ScienceClaimBundle == nil {
		return fmt.Errorf("science_claim_bundle is required")
	}
	if signed.ScienceClaimBundle.SchemaVersion != "" && signed.ScienceClaimBundle.SchemaVersion != SchemaVersionV0 {
		return fmt.Errorf("science_claim_bundle.schema_version %q is not pcs-core canonical (want %q)",
			signed.ScienceClaimBundle.SchemaVersion, SchemaVersionV0)
	}
	if !VerificationPassed(signed.VerificationResult) {
		return fmt.Errorf("embedded verification status is %s (want ProofChecked)", signed.VerificationResult.Status)
	}
	if !opts.VerifyPFDigests {
		return nil
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

// FormatInspectSummary renders a human-readable inspection report with embedded checks.
func FormatInspectSummary(signed *SignedScienceClaimBundle) string {
	return FormatInspectSummaryWithReverify(signed, nil)
}

// FormatInspectSummaryWithReverify renders embedded checks and optional PF re-verification results.
func FormatInspectSummaryWithReverify(signed *SignedScienceClaimBundle, reverify *VerificationResult) string {
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
	appendChecksSection(&b, "Embedded checks", vr.Checks)
	if reverify != nil {
		fmt.Fprintf(&b, "\n")
		appendChecksSection(&b, "PF re-verification", reverify.Checks)
		fmt.Fprintf(&b, "  pf_status:            %s\n", reverify.Status)
	}
	return b.String()
}

func appendChecksSection(b *strings.Builder, title string, checks []VerificationCheck) {
	fmt.Fprintf(b, "%s (%d):\n", title, len(checks))
	for _, c := range checks {
		fmt.Fprintf(b, "  [%s] %s\n", c.Status, c.CheckID)
		fmt.Fprintf(b, "         %s\n", c.Description)
		detailsJSON, _ := json.Marshal(c.Details)
		fmt.Fprintf(b, "         %s\n", string(detailsJSON))
	}
}
