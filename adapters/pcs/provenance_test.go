// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestPFReleaseModeRejectsPlaceholderCommit(t *testing.T) {
	for _, commit := range pcs.ForbiddenPlaceholderCommits {
		if err := pcs.ValidatePFProvenanceCommit(commit, true, false); err == nil {
			t.Fatalf("expected release-mode rejection for %q", commit)
		}
	}
}

func TestPFReleaseModeRejectsLocalDev(t *testing.T) {
	if err := pcs.ValidatePFProvenanceCommit("c20139460f7e46b0fe3031e9da70a1c36e4dda33", true, true); err == nil {
		t.Fatal("expected release-mode + local-dev to be rejected")
	}
}

func TestPFReleaseModeAcceptsRealCommit(t *testing.T) {
	if err := pcs.ValidatePFProvenanceCommit("993a0e5d1214b7c1bd6e84475d771806950965dd", true, false); err != nil {
		t.Fatal(err)
	}
}
