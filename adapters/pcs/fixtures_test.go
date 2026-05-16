// SPDX-License-Identifier: Apache-2.0

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestValidFixtureMatchesBundleSchema(t *testing.T) {
	root := repoRoot(t)
	path := fixturePath(t, "valid_labtrust_bundle.json")
	if err := pcs.ValidateScienceClaimBundleFile(root, path); err != nil {
		t.Fatalf("valid fixture must match schema: %v", err)
	}
}

func TestInvalidFixturesAreRejected(t *testing.T) {
	cases := []struct {
		file    string
		checkID string
	}{
		// May fail schema (required key absent) before presence; either is a valid rejection.
		{"invalid_missing_assumption.json", "pcs.presence.assumption_set"},
		{"invalid_missing_certificate.json", "pcs.presence.trace_certificate"},
		{"invalid_mismatched_trace_hash.json", "pcs.certificate.trace_hash_match"},
		{"invalid_rejected_certificate.json", "pcs.certificate.status_checked"},
		{"invalid_stale_artifact.json", "pcs.artifact.not_stale"},
	}
	for _, tc := range cases {
		t.Run(tc.file, func(t *testing.T) {
			result := verifyFixture(t, tc.file)
			if result.Status != "failed" {
				t.Fatalf("expected failed, got %s", result.Status)
			}
			if tc.file == "invalid_missing_assumption.json" {
				assertAnyFailedCheck(t, result, "pcs.presence.assumption_set", "pcs.schema.science_claim_bundle")
				return
			}
			assertFailedCheck(t, result, tc.checkID)
		})
	}
}

func TestRequiredFourteenChecksEmitted(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json")
	if len(result.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("expected %d checks, got %d", len(pcs.RequiredCheckIDs), len(result.Checks))
	}
	for i, id := range pcs.RequiredCheckIDs {
		if result.Checks[i].CheckID != id {
			t.Fatalf("check %d: expected %s got %s", i, id, result.Checks[i].CheckID)
		}
	}
}
