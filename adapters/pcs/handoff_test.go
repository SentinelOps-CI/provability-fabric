// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func loadedLegacyHandoff(h *pcs.PFHandoff) *pcs.LoadedHandoff {
	return &pcs.LoadedHandoff{Legacy: h}
}

func signWithHandoff(t *testing.T, handoff *pcs.PFHandoff) error {
	t.Helper()
	t.Setenv("PF_DETERMINISTIC", "1")
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)

	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     false,
		Handoff:         loadedLegacyHandoff(handoff),
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		return err
	}
	if !pcs.VerificationPassed(result) {
		return fmt.Errorf("verify status=%s", result.Status)
	}
	_, err = pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: false,
		BundlePath:  path,
		Handoff:     loadedLegacyHandoff(handoff),
	})
	return err
}

func matchingHandoff(t *testing.T) *pcs.PFHandoff {
	t.Helper()
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	h, err := pcs.BuildPFHandoffFromBundle(bundle, path)
	if err != nil {
		t.Fatal(err)
	}
	return h
}

func TestSignAcceptsMatchingHandoff(t *testing.T) {
	if err := signWithHandoff(t, matchingHandoff(t)); err != nil {
		t.Fatal(err)
	}
}

func TestSignRejectsBundleHashNotMatchingHandoff(t *testing.T) {
	h := matchingHandoff(t)
	h.CertifiedBundleHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err := signWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected sign to fail on bundle hash mismatch")
	}
	if !strings.Contains(err.Error(), "certified_bundle_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestSignRejectsCertificateIDNotMatchingHandoff(t *testing.T) {
	h := matchingHandoff(t)
	h.CertificateID = "cert-trace-00000000-0000-0000-0000-000000000000"
	err := signWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected sign to fail on certificate_id mismatch")
	}
	if !strings.Contains(err.Error(), "certificate_id mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestSignRejectsTraceHashNotMatchingHandoff(t *testing.T) {
	h := matchingHandoff(t)
	h.TraceHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err := signWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected sign to fail on trace_hash mismatch")
	}
	if !strings.Contains(err.Error(), "trace_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestLoadPFHandoffFromLabTrustReleaseDir(t *testing.T) {
	ltRelease := filepath.Join(repoRoot(t), "..", "LabTrust-Gym", "examples", "pcs_qc_release", "release")
	handoffPath := filepath.Join(ltRelease, "pf_handoff.json")
	certifiedPath := filepath.Join(ltRelease, "science_claim_bundle.certified.json")
	if _, err := os.Stat(handoffPath); err != nil {
		t.Skip("LabTrust-Gym release pf_handoff.json not present")
	}
	handoff, err := pcs.LoadPFHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	bundle, err := pcs.LoadScienceClaimBundle(certifiedPath)
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.AssertBundleMatchesHandoff(bundle, certifiedPath, handoff); err != nil {
		t.Fatal(err)
	}
}

func writeHandoffFile(t *testing.T, dir string, h *pcs.PFHandoff) string {
	t.Helper()
	path := filepath.Join(dir, "pf_handoff.json")
	data, err := json.MarshalIndent(h, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, data, 0644); err != nil {
		t.Fatal(err)
	}
	return path
}
