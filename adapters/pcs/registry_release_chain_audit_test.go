// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestReleaseChainResultRecordsExecutedRegistryChecks(t *testing.T) {
	result := runLabtrustReleaseChain(t, true)
	var executed int
	for _, c := range result.Checks {
		if !strings.HasPrefix(c.CheckID, "registry.") {
			continue
		}
		exec, _ := c.Details["execution"].(string)
		if exec == pcs.RegistryExecutionPassed || exec == pcs.RegistryExecutionFailed {
			executed++
			if _, ok := c.Details["artifact_type"]; !ok {
				t.Fatalf("registry check %q missing artifact_type", c.CheckID)
			}
		}
	}
	if executed == 0 {
		t.Fatal("expected at least one executed_passed registry semantic check in release chain result")
	}
}

func TestReleaseChainResultRecordsDeferredRegistryChecks(t *testing.T) {
	result := runLabtrustReleaseChain(t, true)
	var deferred int
	for _, c := range result.Checks {
		if !strings.HasPrefix(c.CheckID, "registry.") {
			continue
		}
		if exec, _ := c.Details["execution"].(string); exec == pcs.RegistryExecutionDeferred {
			deferred++
			if _, ok := c.Details["deferral_reason"]; !ok {
				t.Fatalf("deferred check %q missing deferral_reason", c.CheckID)
			}
			if _, ok := c.Details["enforced_by"]; !ok {
				t.Fatalf("deferred check %q missing enforced_by", c.CheckID)
			}
		}
	}
	if deferred == 0 {
		t.Fatal("expected at least one deferred_with_reason registry semantic check")
	}
}

func TestDeferredRegistryCheckRequiresReason(t *testing.T) {
	checks := []pcs.ReleaseValidationCheck{{
		CheckID: "registry.SignedScienceClaimBundle.v0.unknown_check",
		Status:  "passed",
		Details: map[string]any{"execution": pcs.RegistryExecutionDeferred},
	}}
	if err := pcs.ValidateRegistrySemanticCheckRecords(checks); err == nil {
		t.Fatal("expected missing deferral_reason to fail validation")
	}
}

func TestPFExplainReleaseChainOutputsRepairHint(t *testing.T) {
	result := pcs.ReleaseChainValidationResult{
		Status: pcs.StatusRejected,
		Checks: []pcs.ReleaseValidationCheck{{
			CheckID:     "manifest_hashes_match",
			Description: "All manifest artifact hashes match on-disk files",
			Status:      "failed",
			Details:     map[string]any{"failure_code": "PCS_MANIFEST_HASH_MISMATCH"},
		}},
	}
	explanations := pcs.ExplainReleaseChainFailures(result)
	if len(explanations) == 0 || explanations[0].RepairHint == "" {
		t.Fatal("expected release-chain repair hint")
	}
	body := pcs.FormatFailureExplanationsOperational(explanations)
	if !strings.Contains(body, "Repair") || !strings.Contains(body, "Failure") {
		t.Fatalf("expected operational explain layout: %s", body)
	}
	report := pcs.BuildExplainReleaseChainReport(result)
	if report.FailedCount != 1 {
		t.Fatalf("failed_count=%d", report.FailedCount)
	}
}

func TestReleaseModeRejectsUnexplainedDeferredCheck(t *testing.T) {
	checks := []pcs.ReleaseValidationCheck{{
		CheckID: "registry.Test.v0.mystery_defer",
		Status:  "passed",
		Details: map[string]any{
			"execution":            pcs.RegistryExecutionDeferred,
			"release_mode_allowed": false,
		},
	}}
	if !pcs.HasUnexplainedDeferredRegistryCheckForTest(checks, true, false) {
		t.Fatal("expected unexplained deferred check to be rejected in release mode")
	}
}

func TestAdmissionProfileLabtrustQCReleasePasses(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust.qc_release")
	if err != nil {
		t.Fatal(err)
	}
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	handoff, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.EnforceAdmissionProfile(profile, bundle, handoff); err != nil {
		t.Fatalf("labtrust_qc_release profile should pass fixture bundle: %v", err)
	}
	if !profile.ProfileEnforcesRegistryCheck("trace_hash_matches_runtime_receipt") {
		t.Fatal("profile must list trace_hash_matches_runtime_receipt")
	}
	if handoff.Manifest.HandoffKind != "bundle_to_verifier" {
		t.Fatalf("fixture handoff_kind=%q", handoff.Manifest.HandoffKind)
	}
}

func TestUnknownAdmissionProfileRejected(t *testing.T) {
	_, err := pcs.LoadAdmissionProfile("not_a_real_profile")
	if err == nil || !strings.Contains(err.Error(), "unknown admission profile") {
		t.Fatalf("expected unknown profile error, got %v", err)
	}
}

func runLabtrustReleaseChain(t *testing.T, releaseMode bool) pcs.ReleaseChainValidationResult {
	t.Helper()
	artifactDir := labtrustReleaseArtifactDir(t)
	if _, err := os.Stat(filepath.Join(artifactDir, "trace.json")); err != nil {
		t.Skip("full labtrust-release artifact dir required (pcs-core examples/labtrust-release)")
	}
	manifestPath := filepath.Join(artifactDir, "release_manifest.v0.json")
	if _, err := os.Stat(manifestPath); err != nil {
		manifestPath = validReleaseManifestPath(t)
	}
	profile, _ := pcs.LoadAdmissionProfile("labtrust.qc_release")
	opts := pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot(t),
		ArtifactDir:      artifactDir,
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:     loadReleaseManifest(t).PFSourceCommit,
		Registry:         loadArtifactRegistry(t),
		ReleaseMode:      releaseMode,
		AdmissionProfile: profile,
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	return result
}
