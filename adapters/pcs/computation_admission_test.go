// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"path/filepath"
	"strings"
	"testing"
)

func computationFixture(t *testing.T, name string) string {
	t.Helper()
	root, err := FindRepoRoot(filepath.Join("adapters", "pcs"))
	if err != nil {
		t.Fatal(err)
	}
	return filepath.Join(root, "tests", "pcs", "fixtures", "computation", name)
}

func loadComputationProfile(t *testing.T) *AdmissionProfile {
	t.Helper()
	p, err := LoadAdmissionProfile("scientific_computation_reproducibility")
	if err != nil {
		t.Fatal(err)
	}
	if !p.IsComputationProfile() {
		t.Fatal("expected computation profile")
	}
	return p
}

func loadComputationBundle(t *testing.T, name string) *ScienceClaimBundle {
	t.Helper()
	path := computationFixture(t, name)
	bundle, err := LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	return bundle
}

func TestScientificComputationProfileLoads(t *testing.T) {
	p := loadComputationProfile(t)
	if p.WorkflowID != workflowScientificComputationRepro {
		t.Fatalf("workflow_id=%q", p.WorkflowID)
	}
	if len(p.RequiredRuntimeArtifacts) != 4 {
		t.Fatalf("required_runtime_artifacts=%v", p.RequiredRuntimeArtifacts)
	}
}

func computationHandoff(t *testing.T) *LoadedHandoff {
	t.Helper()
	root, err := FindRepoRoot("adapters/pcs")
	if err != nil {
		t.Fatal(err)
	}
	handoff, err := LoadHandoff(filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release", "handoff_to_pf.json"))
	if err != nil {
		t.Fatal(err)
	}
	return handoff
}

func TestValidComputationBundleAdmitted(t *testing.T) {
	profile := loadComputationProfile(t)
	path := computationFixture(t, "valid_computation_bundle.json")
	bundle := loadComputationBundle(t, "valid_computation_bundle.json")
	if err := EnforceAdmissionProfile(profile, path, bundle, computationHandoff(t), true); err != nil {
		t.Fatalf("expected valid computation bundle to pass: %v", err)
	}
}

func TestComputationReleaseChainChecksPassForValidBundle(t *testing.T) {
	profile := loadComputationProfile(t)
	bundle := loadComputationBundle(t, "valid_computation_bundle.json")
	checks, codes := appendComputationReleaseChainChecks(nil, nil, bundle, profile)
	wantIDs := []string{
		"computation_dataset_hash_consistent",
		"computation_environment_hash_consistent",
		"computation_result_hash_consistent",
		"computation_code_commit_present",
		"computation_exit_code_zero",
		"computation_witness_certificate_checked",
	}
	byID := map[string]ReleaseValidationCheck{}
	for _, c := range checks {
		byID[c.CheckID] = c
	}
	for _, id := range wantIDs {
		c, ok := byID[id]
		if !ok {
			t.Fatalf("missing check %q", id)
		}
		if c.Status != "passed" {
			t.Fatalf("check %q status=%q details=%v", id, c.Status, c.Details)
		}
		if len(c.RegistryCheckRefs) == 0 {
			t.Fatalf("check %q missing registry_check_refs", id)
		}
		if c.Details["responsible_component"] != ComponentScientificComputation {
			t.Fatalf("check %q responsible_component=%v", id, c.Details["responsible_component"])
		}
	}
	if len(codes) != 0 {
		t.Fatalf("unexpected failure codes: %v", codes)
	}
	if err := ValidateProfileRequiredRegistryChecks(profile, checks); err != nil {
		t.Fatal(err)
	}
}

func TestComputationAdmissionRejectsInvalidBundles(t *testing.T) {
	profile := loadComputationProfile(t)
	handoff := computationHandoff(t)
	cases := []struct {
		fixture string
		code    string
	}{
		{"missing_dataset_receipt.json", FailureCodeMissingDatasetReceipt},
		{"missing_environment_receipt.json", FailureCodeMissingEnvironmentReceipt},
		{"missing_computation_witness.json", FailureCodeMissingComputationWitness},
		{"rejected_witness.json", FailureCodeRejectedComputationWitness},
		{"result_hash_mismatch.json", FailureCodeResultHashMismatch},
		{"dataset_hash_mismatch.json", FailureCodeDatasetHashMismatch},
		{"missing_code_commit.json", FailureCodeMissingCodeCommit},
		{"nonzero_exit_code.json", FailureCodeNonzeroExitCode},
		{"environment_digest_mismatch.json", FailureCodeEnvironmentDigestMismatch},
	}
	for _, tc := range cases {
		t.Run(tc.fixture, func(t *testing.T) {
			path := computationFixture(t, tc.fixture)
			bundle, err := LoadScienceClaimBundle(path)
			if err != nil {
				t.Fatal(err)
			}
			err = EnforceAdmissionProfile(profile, path, bundle, handoff, true)
			if err == nil || !strings.Contains(err.Error(), tc.code) {
				t.Fatalf("expected %s, got %v", tc.code, err)
			}
		})
	}
}

func TestLabtrustProfileRejectsComputationBundle(t *testing.T) {
	profile, err := LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	path := computationFixture(t, "valid_computation_bundle.json")
	bundle := loadComputationBundle(t, "valid_computation_bundle.json")
	err = EnforceAdmissionProfile(profile, path, bundle, computationHandoff(t), true)
	if err == nil || !strings.Contains(err.Error(), FailureCodeAdmissionProfileWorkflowMismatch) {
		t.Fatalf("expected admission_profile_workflow_mismatch, got %v", err)
	}
}

func TestComputationBundleMatchesSchema(t *testing.T) {
	root, err := FindRepoRoot("adapters/pcs")
	if err != nil {
		t.Fatal(err)
	}
	bundle := loadComputationBundle(t, "valid_computation_bundle.json")
	if err := ValidateComputationProfileBundle(root, bundle); err != nil {
		t.Fatalf("valid computation bundle should match computation profile schema: %v", err)
	}
}

func TestComputationRegistrySemanticChecksExecuted(t *testing.T) {
	root, err := FindRepoRoot("adapters/pcs")
	if err != nil {
		t.Fatal(err)
	}
	registryPath := filepath.Join(root, "tests", "pcs", "fixtures", "computation-release", "artifact_registry.json")
	registry, err := LoadArtifactRegistry(registryPath)
	if err != nil {
		t.Fatal(err)
	}
	releaseDir := filepath.Join(root, "tests", "pcs", "fixtures", "computation-release")
	bundlePath := filepath.Join(releaseDir, "science_claim_bundle.certified.json")
	bundle, err := LoadScienceClaimBundle(bundlePath)
	if err != nil {
		t.Fatal(err)
	}
	if err := HydrateComputationBundleFromDir(bundle, releaseDir); err != nil {
		t.Fatal(err)
	}
	manifestPath := filepath.Join(releaseDir, "release_manifest.v0.json")
	manifest, err := LoadReleaseManifest(manifestPath)
	if err != nil {
		t.Fatal(err)
	}
	ctx := RegistrySemanticAuditContext{
		BaseDir: releaseDir,
		Manifest: manifest,
		Registry: registry,
		Bundle:   bundle,
		Opts: RegistryValidateOptions{
			ReleaseMode: true,
		},
	}
	checks := CollectRegistrySemanticChecks(ctx)
	if len(checks) == 0 {
		t.Fatal("expected registry semantic checks for computation registry")
	}
	foundComputationRegistry := false
	for _, c := range checks {
		if !strings.Contains(c.CheckID, "DatasetReceipt.v0") &&
			!strings.Contains(c.CheckID, "EnvironmentReceipt.v0") &&
			!strings.Contains(c.CheckID, "ComputationWitness.v0") &&
			!strings.Contains(c.CheckID, "ComputationRunReceipt.v0") &&
			!strings.Contains(c.CheckID, "ResultArtifact.v0") {
			continue
		}
		exec, _ := c.Details["execution"].(string)
		if exec == RegistryExecutionPassed || exec == RegistryExecutionDeferred {
			foundComputationRegistry = true
		}
		enforcedBy, _ := c.Details["enforced_by"].(string)
		if strings.HasPrefix(enforcedBy, "computation_") {
			foundComputationRegistry = true
		}
	}
	if !foundComputationRegistry {
		t.Fatal("expected registry semantic audit records for computation artifact types")
	}
}

func TestAgentToolUseRejectsComputationBundle(t *testing.T) {
	profile, err := LoadAdmissionProfile("agent_tool_use_safety")
	if err != nil {
		t.Fatal(err)
	}
	path := computationFixture(t, "valid_computation_bundle.json")
	bundle := loadComputationBundle(t, "valid_computation_bundle.json")
	err = EnforceAdmissionProfile(profile, path, bundle, computationHandoff(t), true)
	if err == nil || !strings.Contains(err.Error(), FailureCodeAdmissionProfileWorkflowMismatch) {
		t.Fatalf("expected admission_profile_workflow_mismatch, got %v", err)
	}
}

func TestComputationExplainRepairHints(t *testing.T) {
	result := ReleaseChainValidationResult{
		Status: "Rejected",
		Checks: []ReleaseValidationCheck{{
			CheckID: "computation_result_hash_consistent",
			Status:  "failed",
			Details: map[string]any{
				"failure_code":          FailureCodeResultHashMismatch,
				"repair_hint":           computationRepairHint,
				"responsible_component": ComponentScientificComputation,
				"registry_check_ref":    "result_hashes_match_result_artifacts",
			},
			RegistryCheckRefs: []string{"result_hashes_match_result_artifacts"},
		}},
	}
	explanations := ExplainReleaseChainFailures(result)
	if len(explanations) == 0 {
		t.Fatal("expected explanations")
	}
	body := FormatFailureExplanations(explanations)
	if !strings.Contains(body, computationRepairHint) {
		t.Fatalf("expected computation repair hint in explain output: %s", body)
	}
}
