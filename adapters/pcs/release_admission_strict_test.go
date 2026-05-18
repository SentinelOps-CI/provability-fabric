// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestReleaseModeStrictRequiresHandoffAndRegistry(t *testing.T) {
	err := pcs.EnforceScienceClaimAdmission(pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, nil, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeReleaseModeHandoffRequired) {
		t.Fatalf("expected handoff required: %v", err)
	}
	handoff, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceScienceClaimAdmission(pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, handoff, nil)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeReleaseModeRegistryRequired) {
		t.Fatalf("expected registry required: %v", err)
	}
}

func TestReleaseModeRejectsLegacyHandoffWithFailureCode(t *testing.T) {
	legacy, err := pcs.LoadHandoff(labtrustReleaseFixture(t, "pf_handoff.json"))
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceScienceClaimAdmission(pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, legacy, loadArtifactRegistry(t))
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeLegacyHandoffForbiddenInReleaseMode) {
		t.Fatalf("expected legacy forbidden: %v", err)
	}
}

func TestReleaseChainResultIncludesRegistrySemanticExecution(t *testing.T) {
	result := runLabtrustReleaseChain(t, true)
	var hasExec, hasDeferred bool
	for _, c := range result.Checks {
		if !strings.HasPrefix(c.CheckID, "registry.") {
			continue
		}
		switch c.Details["execution"] {
		case pcs.RegistryExecutionPassed, pcs.RegistryExecutionFailed:
			hasExec = true
		case pcs.RegistryExecutionDeferred:
			hasDeferred = true
		}
	}
	if !hasExec {
		t.Fatal("expected executed registry semantic checks")
	}
	if !hasDeferred {
		t.Fatal("expected deferred registry semantic checks with catalog")
	}
}

func TestReleaseChainFailedCheckIncludesAuditFields(t *testing.T) {
	result := pcs.ReleaseChainValidationResult{
		Status: pcs.StatusRejected,
		Checks: []pcs.ReleaseValidationCheck{{
			CheckID:     "certificate_id_consistent",
			Description: "Certificate ID is identical across certificate, certified bundle, verification result, and signed bundle",
			Status:      "failed",
			Details: map[string]any{
				"failure_code":        "PCS_CERTIFICATE_ID_MISMATCH",
				"artifact_path":       "science_claim_bundle.certified.json",
				"expected":            "cert-a",
				"actual":              "cert-b",
				"responsible_component": pcs.ComponentLabTrustGym,
			},
		}},
	}
	enriched := pcs.EnrichReleaseChecksWithAudit(result.Checks)
	c := enriched[0]
	if c.Details["repair_hint"] == nil || c.Details["repair_hint"] == "" {
		t.Fatal("expected repair_hint on enriched failed check")
	}
}

func TestAdmissionProfileFromEnv(t *testing.T) {
	t.Setenv("PF_ADMISSION_PROFILE", "labtrust.qc_release")
	profile, err := pcs.AdmissionProfileFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	if profile.ProfileID != "labtrust.qc_release" {
		t.Fatalf("profile_id=%q", profile.ProfileID)
	}
	t.Setenv("PF_ADMISSION_PROFILE", "")
}

func TestGenericToolUseProfileLoads(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("generic_tool_use_trace")
	if err != nil {
		t.Fatal(err)
	}
	if len(profile.RequiredCertificateArtifacts) != 0 {
		t.Fatal("placeholder profile must not require certificates yet")
	}
}
