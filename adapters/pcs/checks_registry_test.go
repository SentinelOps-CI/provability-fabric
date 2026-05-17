// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestVerificationResultCheckOrderMatchesRegistry(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json", false)
	if len(result.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("check count: got %d want %d", len(result.Checks), len(pcs.RequiredCheckIDs))
	}
	for i, id := range pcs.RequiredCheckIDs {
		if result.Checks[i].CheckID != id {
			t.Fatalf("check[%d]: got %q want %q", i, result.Checks[i].CheckID, id)
		}
	}
}

func TestRequiredCheckIDsAreUnique(t *testing.T) {
	seen := make(map[string]struct{}, len(pcs.RequiredCheckIDs))
	for _, id := range pcs.RequiredCheckIDs {
		if _, dup := seen[id]; dup {
			t.Fatalf("duplicate check_id: %s", id)
		}
		seen[id] = struct{}{}
	}
}
