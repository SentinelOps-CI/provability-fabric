// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"errors"
	"fmt"
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

// pcsCoreRoot resolves the pcs-core checkout (PCS_CORE_PATH, repo/pcs-core, or ../pcs-core).
func pcsCoreRoot(t *testing.T) string {
	t.Helper()
	root := repoRoot(t)
	if p := strings.TrimSpace(os.Getenv("PCS_CORE_PATH")); p != "" {
		if st, err := os.Stat(p); err == nil && st.IsDir() {
			return p
		}
	}
	for _, candidate := range []string{
		filepath.Join(root, "pcs-core"),
		filepath.Join(root, "..", "pcs-core"),
	} {
		if st, err := os.Stat(candidate); err == nil && st.IsDir() {
			return candidate
		}
	}
	t.Skip("pcs-core not found (set PCS_CORE_PATH)")
	return ""
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
		SourceCommit:    "cccccccccccccccccccccccccccccccccccccccc",
		LocalDev:        localDev,
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatalf("verify %s: %v", name, err)
	}
	return result
}

func labtrustFixture(t *testing.T, name string) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust", name)
}

func TestVerifyPCSCoreCanonicalBundlePasses(t *testing.T) {
	result := verifyFixture(t, filepath.Join("fixtures", "labtrust", "science_claim_bundle.certified.json"), false)
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected ProofChecked, got %s", result.Status)
	}
}

func TestVerifyValidLabtrustBundlePasses(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json", false)
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected ProofChecked, got %s", result.Status)
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
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertAnyFailedCheck(t, result, "assumption_set_present", "science_claim_bundle_schema")
}

func TestVerifyMissingCertificateFails(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_certificate.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_certificate_present")
}

func TestVerifyMismatchedTraceHashFails(t *testing.T) {
	result := verifyFixture(t, "invalid_mismatched_trace_hash.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_hash_alignment")
}

func TestVerifyRejectedCertificateFails(t *testing.T) {
	result := verifyFixture(t, "invalid_rejected_certificate.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "certificate_status_checked")
	assertCheckReasonCode(t, result, "certificate_status_checked", pcs.ReasonCertificateRejected)
}

func TestVerifyStaleArtifactFails(t *testing.T) {
	result := verifyFixture(t, "invalid_stale_artifact.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "artifact_not_stale")
}

func TestVerifyZeroSourceCommitFailsInReleaseMode(t *testing.T) {
	result := verifyFixture(t, "invalid_zero_source_commit_release.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "source_commit_not_placeholder")
}

func TestVerifyZeroSourceCommitAllowedInLocalDev(t *testing.T) {
	result := verifyFixture(t, "invalid_zero_source_commit_release.json", true)
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected ProofChecked with local_dev, got %s", result.Status)
	}
}

func TestSignPassedBundleEmitsSignedBundle(t *testing.T) {
	path := fixturePath(t, "valid_labtrust_bundle.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
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
	if !pcs.VerificationPassed(signed.VerificationResult) {
		t.Fatal("verification_result must be ProofChecked")
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
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
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || pcs.VerificationPassed(result) {
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
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, _ := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	summary := pcs.FormatInspectSummary(signed)
	wantChecks := fmt.Sprintf("Embedded checks (%d):", len(pcs.RequiredCheckIDs))
	if !strings.Contains(summary, wantChecks) {
		t.Fatalf("inspect must print all checks, got:\n%s", summary)
	}
	for _, id := range pcs.RequiredCheckIDs {
		if !strings.Contains(summary, id) {
			t.Fatalf("inspect missing check_id %s", id)
		}
	}
}

func TestVerifyLegacySingularRuntimeReceiptFails(t *testing.T) {
	_, err := pcs.LoadScienceClaimBundle(fixturePath(t, "invalid_legacy_singular_runtime_receipt.json"))
	if err == nil {
		t.Fatal("expected legacy bundle load to fail")
	}
	var legacy *pcs.LegacyBundleError
	if !errors.As(err, &legacy) {
		t.Fatalf("expected LegacyBundleError, got %v", err)
	}
}

func TestVerifySchemaVersionArtifactNameFails(t *testing.T) {
	_, err := pcs.LoadScienceClaimBundle(fixturePath(t, "invalid_schema_version_artifact_name.json"))
	if err == nil {
		t.Fatal("expected legacy schema_version to fail at load")
	}
	var legacy *pcs.LegacyBundleError
	if !errors.As(err, &legacy) {
		t.Fatalf("expected LegacyBundleError, got %v", err)
	}
}

func TestVerifyRuntimeReceiptsArrayRequired(t *testing.T) {
	_, err := pcs.LoadScienceClaimBundle(fixturePath(t, "invalid_missing_runtime_receipts.json"))
	if err == nil {
		result := verifyFixture(t, "invalid_missing_runtime_receipts.json", false)
		if pcs.VerificationPassed(result) {
			t.Fatal("expected verification to fail without runtime_receipts")
		}
		return
	}
}

func TestVerifyCertificatesArrayRequiredForCertifiedBundle(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_certificate.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_certificate_present")
}

func TestVerifyRuntimeReceiptCountExactlyOneFails(t *testing.T) {
	result := verifyFixture(t, "invalid_multiple_runtime_receipts.json", false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
	assertFailedCheck(t, result, "runtime_receipt_present")
	assertCheckReasonCode(t, result, "runtime_receipt_present", pcs.ReasonRuntimeReceiptCount)
}

func TestSignOutputsPCSCoreSignedBundle(t *testing.T) {
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	if signed.SchemaVersion != pcs.SchemaVersionV0 {
		t.Fatalf("signed schema_version want v0, got %s", signed.SchemaVersion)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed schema: %v", err)
	}
}

func TestInspectAcceptsPCSCoreSignedBundle(t *testing.T) {
	path := labtrustFixture(t, "signed_science_claim_bundle.json")
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed schema: %v", err)
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: false}); err != nil {
		t.Fatalf("inspect integrity: %v", err)
	}
	summary := pcs.FormatInspectSummary(signed)
	if !strings.Contains(summary, "scb-qc-release-v0.1") || !strings.Contains(summary, "ProofChecked") {
		t.Fatalf("inspect summary missing signed bundle fields: %s", summary)
	}
	// pcs-core frozen signed bundles may embed fewer checks than the current PF verifier.
	if !strings.Contains(summary, "Embedded checks (") {
		t.Fatalf("inspect summary missing embedded checks: %s", summary)
	}
}

func TestReverifyCorruptedBundleRejected(t *testing.T) {
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	if len(bundle.Certificates) == 0 {
		t.Fatal("expected certificate")
	}
	bundle.Certificates[0].TraceHash = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundleValue(bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected after trace hash corruption, got %s", result.Status)
	}
	assertFailedCheck(t, result, "trace_hash_alignment")
}

func TestInspectReverifyRunsFifteenChecks(t *testing.T) {
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundleValue(bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("reverify: %v status=%s", err, result.Status)
	}
	if len(result.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("expected %d checks, got %d", len(pcs.RequiredCheckIDs), len(result.Checks))
	}
}

func TestVerificationResultSnapshot(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json", false)
	result.VerificationID = "verification-00000000-0000-0000-0000-000000000001"
	result.CreatedAt = "2026-05-16T12:00:00Z"
	result.SourceCommit = "cccccccccccccccccccccccccccccccccccccccc"
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
