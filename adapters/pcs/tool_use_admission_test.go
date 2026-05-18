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

func TestToolUseProfileSkipsHandoffRegistryInReleaseMode(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	err := pcs.EnforceScienceClaimAdmission(pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, nil, nil, profile)
	if err != nil {
		t.Fatalf("tool-use skeleton should skip handoff/registry: %v", err)
	}
}

func TestLabtrustQCReleaseProfileLoads(t *testing.T) {
	p, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	if p.StatusPolicy == "" || p.RepairHintPolicy == "" {
		t.Fatal("profile must include status_policy and repair_hint_policy")
	}
	if len(p.RequiredHandoffKinds) == 0 {
		t.Fatal("required_handoff_kinds must be set")
	}
}

func TestAgentToolUseSafetyProfileLoads(t *testing.T) {
	p := loadAgentToolUseProfile(t)
	if !p.IsToolUseProfile() {
		t.Fatal("expected tool-use profile")
	}
}

func TestAgentToolUseRejectsScienceClaimShape(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	path := toolUseFixture(t, "incomplete_science_claim_shape.json")
	err := pcs.EnforceAdmissionProfile(profile, path, nil, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeMissingToolUseTrace) {
		t.Fatalf("expected missing_tool_use_trace, got %v", err)
	}
}

func TestAgentToolUseRejectsMissingCertificate(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	err := pcs.EnforceAdmissionProfile(profile, toolUseFixture(t, "missing_certificate.json"), nil, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeMissingToolUseCertificate) {
		t.Fatalf("expected missing_tool_use_certificate, got %v", err)
	}
}

func TestAgentToolUseRejectsRejectedCertificate(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	err := pcs.EnforceAdmissionProfile(profile, toolUseFixture(t, "rejected_certificate.json"), nil, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeToolUseCertificateRejected) {
		t.Fatalf("expected tool_use_certificate_rejected, got %v", err)
	}
}

func TestAgentToolUseRejectsTraceHashMismatch(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	err := pcs.EnforceAdmissionProfile(profile, toolUseFixture(t, "trace_hash_mismatch.json"), nil, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeToolTraceHashMismatch) {
		t.Fatalf("expected tool_trace_hash_mismatch, got %v", err)
	}
}

func TestAgentToolUseRejectsUnauthorizedViolation(t *testing.T) {
	profile := loadAgentToolUseProfile(t)
	err := pcs.EnforceAdmissionProfile(profile, toolUseFixture(t, "unauthorized_violation.json"), nil, nil)
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
