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

func passCheck(id, description string, details map[string]any) VerificationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return VerificationCheck{CheckID: id, Description: description, Status: CheckPassed, Details: details}
}

func failCheck(id, description, reasonCode string, details map[string]any) VerificationCheck {
	return VerificationCheck{CheckID: id, Description: description, Status: CheckFailed, Details: withReason(reasonCode, details)}
}

func skipCheck(id, description string, details map[string]any) VerificationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return VerificationCheck{CheckID: id, Description: description, Status: CheckSkipped, Details: details}
}

func detailMsg(msg string) map[string]any {
	return map[string]any{"message": msg}
}

// BuildVerificationResult constructs VerificationResult (schema_version v0).
func BuildVerificationResult(bundle *ScienceClaimBundle, checks []VerificationCheck, verifierVersion, sourceCommit string) VerificationResult {
	// pcs-core VerificationResult.status uses artifact_status enum (not "passed"/"failed").
	status := "ProofChecked"
	for _, c := range checks {
		if c.Status == CheckFailed {
			status = "Rejected"
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
		SchemaVersion:   SchemaVersionV0,
		VerificationID:  fmt.Sprintf("verification-%s", uuid.NewString()),
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
		return "0000000000000000000000000000000000000001"
	}
	commit := strings.TrimSpace(string(out))
	if len(commit) < 7 {
		return "0000000000000000000000000000000000000001"
	}
	return commit
}

// VerificationPassed reports whether all required checks passed (pcs-core artifact_status).
func VerificationPassed(result VerificationResult) bool {
	return result.Status == "ProofChecked"
}

// FailedChecks returns checks that did not pass.
func FailedChecks(result VerificationResult) []VerificationCheck {
	var failed []VerificationCheck
	for _, c := range result.Checks {
		if c.Status == CheckFailed {
			failed = append(failed, c)
		}
	}
	return failed
}
