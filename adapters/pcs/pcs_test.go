// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func repoRoot(t *testing.T) string {
	t.Helper()
	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	root, err := pcs.FindRepoRoot(wd)
	if err != nil {
		root, err = pcs.FindRepoRoot(filepath.Join(wd, "..", ".."))
	}
	if err != nil {
		t.Fatal(err)
	}
	return root
}

func fixturePath(t *testing.T, name string) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "tests", "pcs", name)
}

func verifyFixture(t *testing.T, name string, localDev bool) pcs.VerificationResult {
	t.Helper()
	path := fixturePath(t, name)
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatalf("load %s: %v", name, err)
	}
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "test-commit",
		LocalDev:        localDev,
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatalf("verify %s: %v", name, err)
	}
	return result
}

func TestVerifyValidLabtrustBundlePasses(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json", false)
	if result.Status != "passed" {
		t.Fatalf("expected passed, got %s", result.Status)
	}
	if result.SchemaVersion != pcs.SchemaVersionV0 {
		t.Fatalf("expected schema_version v0, got %s", result.SchemaVersion)
	}
	if len(result.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("expected %d checks, got %d", len(pcs.RequiredCheckIDs), len(result.Checks))
	}
}

func TestVerifyMissingAssumptionFails(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_assumption.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertAnyFailedCheck(t, result, "assumption_set_present", "science_claim_bundle_schema")
}

func TestVerifyMissingCertificateFails(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_certificate.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_certificate_present")
}

func TestVerifyMismatchedTraceHashFails(t *testing.T) {
	result := verifyFixture(t, "invalid_mismatched_trace_hash.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_hash_alignment")
}

func TestVerifyRejectedCertificateFails(t *testing.T) {
	result := verifyFixture(t, "invalid_rejected_certificate.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "certificate_status_checked")
	assertCheckReasonCode(t, result, "certificate_status_checked", pcs.ReasonCertificateRejected)
}

func TestVerifyStaleArtifactFails(t *testing.T) {
	result := verifyFixture(t, "invalid_stale_artifact.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "artifact_not_stale")
}

func TestVerifyZeroSourceCommitFailsInReleaseMode(t *testing.T) {
	result := verifyFixture(t, "invalid_zero_source_commit_release.json", false)
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "source_commit_not_placeholder")
}

func TestVerifyZeroSourceCommitAllowedInLocalDev(t *testing.T) {
	result := verifyFixture(t, "invalid_zero_source_commit_release.json", true)
	if result.Status != "passed" {
		t.Fatalf("expected passed with local_dev, got %s", result.Status)
	}
}

func TestSignPassedBundleEmitsSignedBundle(t *testing.T) {
	path := fixturePath(t, "valid_labtrust_bundle.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "test"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || result.Status != "passed" {
		t.Fatalf("verification failed: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	if signed.SchemaVersion != pcs.SchemaVersionV0 {
		t.Fatalf("expected signed schema_version v0")
	}
	if signed.ScienceClaimBundle == nil {
		t.Fatal("science_claim_bundle required for Scientific Memory import")
	}
	if signed.VerificationResult.Status != "passed" {
		t.Fatal("verification_result must be passed")
	}
	if err := pcs.VerifySignedBundleIntegrity(signed); err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed schema: %v", err)
	}
}

func TestSignFailedBundleRefuses(t *testing.T) {
	path := fixturePath(t, "invalid_missing_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "test"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || result.Status != "failed" {
		t.Fatalf("expected failed verification")
	}
	if _, err := pcs.SignVerificationResult(root, bundle, result); err == nil {
		t.Fatal("expected sign to refuse failed verification")
	}
}

func TestInspectPrintsCheckSummary(t *testing.T) {
	path := fixturePath(t, "valid_labtrust_bundle.json")
	bundle, _ := pcs.LoadScienceClaimBundle(path)
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "test"}
	result, _ := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	summary := pcs.FormatInspectSummary(signed)
	if !strings.Contains(summary, "Checks (15):") {
		t.Fatalf("inspect must print all checks, got:\n%s", summary)
	}
	for _, id := range pcs.RequiredCheckIDs {
		if !strings.Contains(summary, id) {
			t.Fatalf("inspect missing check_id %s", id)
		}
	}
}

func TestVerificationResultSnapshot(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json", false)
	result.VerificationID = "verification-00000000-0000-0000-0000-000000000001"
	result.CreatedAt = "2026-05-16T12:00:00Z"
	result.SourceCommit = "test-commit"
	result.SignatureOrDigest = "sha256:snapshot-digest"

	data, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	snapshot := filepath.Join(repoRoot(t), "tests", "pcs", "testdata", "valid_verification_result.snapshot.json")
	if os.Getenv("UPDATE_PCS_SNAPSHOTS") == "1" {
		_ = os.MkdirAll(filepath.Dir(snapshot), 0755)
		if err := os.WriteFile(snapshot, data, 0644); err != nil {
			t.Fatal(err)
		}
		return
	}
	expected, err := os.ReadFile(snapshot)
	if err != nil {
		t.Fatalf("missing snapshot %s (run with UPDATE_PCS_SNAPSHOTS=1): %v", snapshot, err)
	}
	if strings.TrimSpace(string(expected)) != strings.TrimSpace(string(data)) {
		t.Fatalf("snapshot mismatch for valid bundle verification result")
	}
}

func assertFailedCheck(t *testing.T, result pcs.VerificationResult, id string) {
	t.Helper()
	assertAnyFailedCheck(t, result, id)
}

func assertCheckReasonCode(t *testing.T, result pcs.VerificationResult, checkID, reason string) {
	t.Helper()
	for _, c := range result.Checks {
		if c.CheckID == checkID {
			code, _ := c.Details["reason_code"].(string)
			if code != reason {
				t.Fatalf("check %s: expected reason_code %s, got %s", checkID, reason, code)
			}
			return
		}
	}
	t.Fatalf("check %s not found", checkID)
}

func assertAnyFailedCheck(t *testing.T, result pcs.VerificationResult, ids ...string) {
	t.Helper()
	for _, id := range ids {
		for _, c := range result.Checks {
			if c.CheckID == id && c.Status == pcs.CheckFailed {
				return
			}
		}
	}
	t.Fatalf("expected one of %v to fail in %+v", ids, result.Checks)
}
