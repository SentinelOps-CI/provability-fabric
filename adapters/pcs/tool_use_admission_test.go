// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func toolUseFixture(t *testing.T, name string) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "tool-use", name)
}

func loadAgentToolUseProfile(t *testing.T) *pcs.AdmissionProfile {
	t.Helper()
	p, err := pcs.LoadAdmissionProfile("agent_tool_use_safety")
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func toolUseHandoff(t *testing.T) *pcs.LoadedHandoff {
	t.Helper()
	h, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	return h
}

func TestReleaseModeRequiresAdmissionProfile(t *testing.T) {
	_, err := pcs.ResolveAdmissionProfileForReleaseMode("", true)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeMissingAdmissionProfile) {
		t.Fatalf("expected missing_admission_profile, got %v", err)
	}
}

func TestUnknownAdmissionProfileRejected(t *testing.T) {
	_, err := pcs.ResolveAdmissionProfileForReleaseMode("not_a_real_profile_xyz", true)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeUnknownAdmissionProfile) {
		t.Fatalf("expected unknown_admission_profile, got %v", err)
	}
}

func TestLoadAdmissionProfileFromRepoPath(t *testing.T) {
	root := repoRoot(t)
	path := filepath.Join(root, "adapters", "pcs", "admission_profiles", "labtrust_qc_release.json")
	p, err := pcs.LoadAdmissionProfileFromPath(path)
	if err != nil {
		t.Fatal(err)
	}
	if p.ProfileID != "labtrust_qc_release" || p.WorkflowID == "" {
		t.Fatalf("unexpected profile: %+v", p)
	}
}

func TestAdmissionProfilesMatchSchema(t *testing.T) {
	for _, id := range []string{"labtrust_qc_release", "agent_tool_use_safety"} {
		p, err := pcs.LoadAdmissionProfile(id)
		if err != nil {
			t.Fatalf("profile %s: %v", id, err)
		}
		if err := pcs.ValidateAdmissionProfile(p); err != nil {
			t.Fatalf("profile %s invalid: %v", id, err)
		}
	}
}

func TestLabtrustQCReleaseProfileLoads(t *testing.T) {
	p, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	if p.WorkflowID != "labtrust.qc_release_v0" {
		t.Fatalf("workflow_id=%q", p.WorkflowID)
	}
	if p.StatusPolicy == "" || p.RepairHintPolicy == "" {
		t.Fatal("profile must include status_policy and repair_hint_policy")
	}
}

func TestAgentToolUseSafetyProfileLoads(t *testing.T) {
	p := loadAgentToolUseProfile(t)
	if !p.IsToolUseProfile() {
		t.Fatal("expected tool-use profile")
	}
	if p.WorkflowID != "agent_tool_use.safety_v0" {
		t.Fatalf("workflow_id=%q", p.WorkflowID)
	}
	if p.AcceptedBundleArtifact != "ScienceClaimBundle.v0" {
		t.Fatalf("accepted_bundle_artifact=%q", p.AcceptedBundleArtifact)
	}
}

func TestAgentToolUseRejectsLabtrustShapedBundle(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "incomplete_science_claim_shape.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeAdmissionProfileWorkflowMismatch) {
		t.Fatalf("expected admission_profile_workflow_mismatch, got %v", err)
	}
}

func TestLabtrustProfileRejectsToolUseBundle(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	path := toolUseFixture(t, "missing_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeAdmissionProfileWorkflowMismatch) {
		t.Fatalf("expected admission_profile_workflow_mismatch, got %v", err)
	}
}

func TestAgentToolUseRejectsMissingCertificate(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "missing_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeMissingToolUseCertificate) {
		t.Fatalf("expected missing_tool_use_certificate, got %v", err)
	}
}

func TestAgentToolUseRejectsRejectedCertificate(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "rejected_certificate.json")
	bundle, _ := pcs.LoadScienceClaimBundle(path)
	err := pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeToolUseCertificateRejected) {
		t.Fatalf("expected tool_use_certificate_rejected, got %v", err)
	}
}

func TestAgentToolUseRejectsTraceHashMismatch(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "trace_hash_mismatch.json")
	bundle, _ := pcs.LoadScienceClaimBundle(path)
	err := pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeToolTraceHashMismatch) {
		t.Fatalf("expected tool_trace_hash_mismatch, got %v", err)
	}
}

func TestAgentToolUseRejectsPolicyHashMismatch(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "policy_hash_mismatch.json")
	bundle, _ := pcs.LoadScienceClaimBundle(path)
	err := pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodePolicyHashMismatch) {
		t.Fatalf("expected policy_hash_mismatch, got %v", err)
	}
}

func TestAgentToolUseRejectsUnauthorizedViolation(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "unauthorized_violation.json")
	bundle, _ := pcs.LoadScienceClaimBundle(path)
	err := pcs.EnforceAdmissionProfile(profile, path, bundle, toolUseHandoff(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeUnauthorizedToolCallViolation) {
		t.Fatalf("expected unauthorized_tool_call_certificate_violation, got %v", err)
	}
}

func TestAdmissionProfileLabtrustQCReleasePasses(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
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
	if err := pcs.EnforceAdmissionProfile(profile, path, bundle, handoff); err != nil {
		t.Fatalf("labtrust_qc_release profile should pass fixture bundle: %v", err)
	}
}

func TestReleaseChainResultIncludesAdmissionProfileCheck(t *testing.T) {
	result := runLabtrustReleaseChain(t, true)
	found := false
	for _, c := range result.Checks {
		if c.CheckID == "admission_profile_selected" && c.Status == "passed" {
			found = true
			break
		}
	}
	if !found {
		t.Fatal("expected admission_profile_selected in release chain result")
	}
}
