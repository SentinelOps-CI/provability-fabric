// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"time"

	"github.com/google/uuid"
)

func passCheck(id, description, details string) VerificationCheck {
	return VerificationCheck{CheckID: id, Description: description, Status: CheckPassed, Details: details}
}

func failCheck(id, description, details string) VerificationCheck {
	return VerificationCheck{CheckID: id, Description: description, Status: CheckFailed, Details: details}
}

func skipCheck(id, description, details string) VerificationCheck {
	return VerificationCheck{CheckID: id, Description: description, Status: CheckSkipped, Details: details}
}

// BuildVerificationResult constructs VerificationResult.v0 from completed checks.
func BuildVerificationResult(bundle *ScienceClaimBundle, checks []VerificationCheck, verifierVersion, sourceCommit string) VerificationResult {
	status := "passed"
	for _, c := range checks {
		if c.Status == CheckFailed {
			status = "failed"
			break
		}
	}
	bundleID := ""
	if bundle != nil {
		bundleID = bundle.BundleID
	}
	if verifierVersion == "" {
		verifierVersion = DefaultVerifierVersion
	}
	if sourceCommit == "" {
		sourceCommit = ResolveSourceCommit()
	}
	result := VerificationResult{
		VerificationID:  uuid.NewString(),
		SchemaVersion:   SchemaVerificationResult,
		BundleID:        bundleID,
		Verifier:        VerifierName,
		VerifierVersion: verifierVersion,
		Status:          status,
		Checks:          checks,
		CreatedAt:       time.Now().UTC().Format(time.RFC3339),
		SourceRepo:      VerifierSourceRepo,
		SourceCommit:    sourceCommit,
	}
	result.SignatureOrDigest = DigestVerificationResult(result)
	return result
}

// DigestVerificationResult returns sha256 of canonical verification JSON without signature field.
func DigestVerificationResult(result VerificationResult) string {
	copy := result
	copy.SignatureOrDigest = ""
	payload, err := CanonicalJSON(copy)
	if err != nil {
		return ""
	}
	return "sha256:" + SHA256Hex(payload)
}

// SHA256Hex hashes bytes to lowercase hex.
func SHA256Hex(data []byte) string {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}

// ResolveSourceCommit returns git HEAD or PF_SOURCE_COMMIT when available.
func ResolveSourceCommit() string {
	if v := strings.TrimSpace(os.Getenv("PF_SOURCE_COMMIT")); v != "" {
		return v
	}
	out, err := exec.Command("git", "rev-parse", "HEAD").Output()
	if err != nil {
		return "unknown"
	}
	return strings.TrimSpace(string(out))
}

// SignVerificationResult builds a SignedScienceClaimBundle for import by Scientific Memory.
func SignVerificationResult(repoRoot, bundlePath string, bundle *ScienceClaimBundle, result VerificationResult) (*SignedScienceClaimBundle, error) {
	if !VerificationPassed(result) {
		return nil, fmt.Errorf("cannot sign: verification status is %s", result.Status)
	}
	digest, err := BundleDigest(bundlePath)
	if err != nil {
		return nil, fmt.Errorf("bundle digest: %w", err)
	}
	signed := &SignedScienceClaimBundle{
		SchemaVersion:      SchemaSignedScienceClaim,
		BundleID:           result.BundleID,
		BundleDigest:       "sha256:" + digest,
		SignedAt:           time.Now().UTC().Format(time.RFC3339),
		ScienceClaimBundle: bundle,
		VerificationResult: result,
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

// VerificationPassed reports whether all required checks passed.
func VerificationPassed(result VerificationResult) bool {
	return result.Status == "passed"
}

// FormatInspectSummary renders a human-readable inspection report.
func FormatInspectSummary(signed *SignedScienceClaimBundle) string {
	var b strings.Builder
	vr := signed.VerificationResult
	fmt.Fprintf(&b, "Signed Science Claim Bundle\n")
	fmt.Fprintf(&b, "  bundle_id:          %s\n", signed.BundleID)
	fmt.Fprintf(&b, "  bundle_digest:      %s\n", signed.BundleDigest)
	fmt.Fprintf(&b, "  signed_at:          %s\n", signed.SignedAt)
	fmt.Fprintf(&b, "  verification_id:    %s\n", vr.VerificationID)
	fmt.Fprintf(&b, "  verifier:           %s %s\n", vr.Verifier, vr.VerifierVersion)
	fmt.Fprintf(&b, "  verification_status: %s\n", vr.Status)
	fmt.Fprintf(&b, "  result_digest:      %s\n", vr.SignatureOrDigest)
	fmt.Fprintf(&b, "  wrapper_digest:     %s\n\n", signed.SignatureOrDigest)
	fmt.Fprintf(&b, "Checks (%d):\n", len(vr.Checks))
	for _, c := range vr.Checks {
		fmt.Fprintf(&b, "  [%s] %s\n", c.Status, c.CheckID)
		fmt.Fprintf(&b, "         %s\n", c.Description)
		if c.Details != "" {
			fmt.Fprintf(&b, "         %s\n", c.Details)
		}
	}
	return b.String()
}
