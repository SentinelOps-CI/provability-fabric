// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestFormalCheckAdmissionRejectsMissingLeanResult(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	manifest, err := pcs.LoadReleaseManifest(labtrustReleaseFixture(t, "release_manifest.v0.json"))
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceFormalCheckAdmission(profile, manifest, pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, pcs.FormalCheckInputs{})
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeMissingLeanCheckResult) {
		t.Fatalf("expected missing_lean_check_result, got %v", err)
	}
}

func TestFormalCheckAdmissionAcceptsLabtrustFixtures(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	manifest, err := pcs.LoadReleaseManifest(labtrustReleaseFixture(t, "release_manifest.v0.json"))
	if err != nil {
		t.Fatal(err)
	}
	formal := loadFormalCheckInputs(t, "labtrust")
	if err := pcs.EnforceFormalCheckAdmission(profile, manifest, pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, formal); err != nil {
		t.Fatal(err)
	}
}

func TestFormalReleaseChainChecksIncludeCertificateMatchesRuntime(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	manifest, err := pcs.LoadReleaseManifest(labtrustReleaseFixture(t, "release_manifest.v0.json"))
	if err != nil {
		t.Fatal(err)
	}
	formal := loadFormalCheckInputs(t, "labtrust")
	checks, codes := pcs.AppendFormalReleaseChainChecks(profile, manifest, formal, nil, nil)
	if len(codes) > 0 {
		t.Fatalf("unexpected failure codes: %v", codes)
	}
	found := false
	for _, c := range checks {
		if c.CheckID == "formal.CertificateMatchesRuntime" && c.Status == "passed" {
			found = true
			th, _ := c.Details["lean_theorem"].(string)
			if th != "admissible_release_has_matching_trace_hash" {
				t.Fatalf("unexpected theorem: %s", th)
			}
		}
	}
	if !found {
		t.Fatal("expected formal.CertificateMatchesRuntime passed check")
	}
}

func TestFormalCheckRejectsUnauthorizedTheorem(t *testing.T) {
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	manifest, err := pcs.LoadReleaseManifest(labtrustReleaseFixture(t, "release_manifest.v0.json"))
	if err != nil {
		t.Fatal(err)
	}
	formal := loadFormalCheckInputs(t, "labtrust")
	formal.LeanCheckResult.ObligationResults[0].LeanTheorem = "not_a_real_theorem"
	err = pcs.EnforceFormalCheckAdmission(profile, manifest, pcs.ReleaseAdmissionPolicy{ReleaseMode: true}, formal)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeUnauthorizedLeanTheorem) {
		t.Fatalf("expected unauthorized_lean_theorem, got %v", err)
	}
}

func TestExplainFormalLeanFailure(t *testing.T) {
	check := pcs.ReleaseValidationCheck{
		CheckID:     "formal.CertificateMatchesRuntime",
		Description: "Lean trust kernel established CertificateMatchesRuntime",
		Status:      "failed",
		Details: map[string]any{
			"expected_predicate": "certificate.trace_hash = runtime_receipt.trace_hash",
			"actual_values": map[string]any{
				"certificate_trace_hash":       "sha256:aaa",
				"runtime_receipt_trace_hash": "sha256:bbb",
			},
			"lean_theorem":          "admissible_release_has_matching_trace_hash",
			"obligation_id":         "trace_hash_alignment",
			"failure_code":          pcs.FailureCodeLeanCheckFailed,
			"responsible_component": pcs.ComponentLeanTrustKernel,
		},
	}
	exp, ok := pcs.FormalFailureExplanation(check)
	if !ok {
		t.Fatal("expected formal explanation")
	}
	if !strings.Contains(exp.RepairHint, "CertificateMatchesRuntime") {
		t.Fatalf("unexpected repair hint: %s", exp.RepairHint)
	}
	_ = filepath.Base("lean_check_result.v0.json")
	explanations := pcs.ExplainReleaseChainFailures(pcs.ReleaseChainValidationResult{
		Checks: []pcs.ReleaseValidationCheck{check},
	})
	if len(explanations) != 1 || !strings.Contains(explanations[0].RepairHint, "trace_hash") {
		t.Fatalf("explain release chain: %+v", explanations)
	}
}
