// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

type releaseFixtureManifest struct {
	PFSourceCommit string `json:"pf_source_commit"`
}

func loadReleaseManifest(t *testing.T) releaseFixtureManifest {
	t.Helper()
	data, err := os.ReadFile(labtrustReleaseFixture(t, "FIXTURE_MANIFEST.json"))
	if err != nil {
		t.Fatal(err)
	}
	var m releaseFixtureManifest
	if err := json.Unmarshal(data, &m); err != nil {
		t.Fatal(err)
	}
	if m.PFSourceCommit == "" {
		t.Fatal("FIXTURE_MANIFEST.json missing pf_source_commit")
	}
	return m
}

func TestPFReleaseCertificateIDChain(t *testing.T) {
	certified, err := pcs.LoadScienceClaimBundle(labtrustReleaseFixture(t, "science_claim_bundle.certified.json"))
	if err != nil {
		t.Fatal(err)
	}
	vrBytes, err := os.ReadFile(labtrustReleaseFixture(t, "verification_result.json"))
	if err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	var result pcs.VerificationResult
	if err := json.Unmarshal(vrBytes, &result); err != nil {
		t.Fatal(err)
	}
	if err := pcs.AssertReleaseArtifactChain(certified, result, signed); err != nil {
		t.Fatal(err)
	}
}

func TestPFReleaseFixtureHasRealSourceCommit(t *testing.T) {
	manifest := loadReleaseManifest(t)
	for _, name := range []string{"verification_result.json", "signed_science_claim_bundle.json"} {
		path := labtrustReleaseFixture(t, name)
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if containsForbiddenCommit(string(data)) {
			t.Fatalf("%s contains forbidden placeholder PF source_commit", name)
		}
	}
	if pcs.IsForbiddenPlaceholderCommit(manifest.PFSourceCommit) {
		t.Fatalf("manifest pf_source_commit is placeholder: %q", manifest.PFSourceCommit)
	}
}

func TestPFVerificationResultSourceCommitMatchesManifest(t *testing.T) {
	manifest := loadReleaseManifest(t)
	data, err := os.ReadFile(labtrustReleaseFixture(t, "verification_result.json"))
	if err != nil {
		t.Fatal(err)
	}
	var result pcs.VerificationResult
	if err := json.Unmarshal(data, &result); err != nil {
		t.Fatal(err)
	}
	if result.SourceCommit != manifest.PFSourceCommit {
		t.Fatalf("verification_result.source_commit %q != manifest %q",
			result.SourceCommit, manifest.PFSourceCommit)
	}
}

func TestPFSignedBundleSourceCommitMatchesManifest(t *testing.T) {
	manifest := loadReleaseManifest(t)
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed.SourceCommit != manifest.PFSourceCommit {
		t.Fatalf("signed wrapper source_commit %q != manifest %q", signed.SourceCommit, manifest.PFSourceCommit)
	}
	if signed.VerificationResult.SourceCommit != manifest.PFSourceCommit {
		t.Fatalf("embedded verification_result.source_commit %q != manifest %q",
			signed.VerificationResult.SourceCommit, manifest.PFSourceCommit)
	}
}

func containsForbiddenCommit(body string) bool {
	for _, p := range pcs.ForbiddenPlaceholderCommits {
		if strings.Contains(body, `"source_commit": "`+p+`"`) ||
			strings.Contains(body, `"source_commit":"`+p+`"`) {
			return true
		}
	}
	return false
}
