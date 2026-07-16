// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//go:build pcsbench

package pcs_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func writeJSONFixture(path string, v any) error {
	data, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return err
	}
	data = append(data, '\n')
	return os.WriteFile(path, data, 0o644)
}

func TestReleaseDeterministicSignIDsStable(t *testing.T) {
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	t.Setenv("PF_DETERMINISTIC", "1")
	id1, sid1 := releaseDeterministicGoldenIDs(manifest.PFSourceCommit, t)
	id2, sid2 := releaseDeterministicGoldenIDs(manifest.PFSourceCommit, t)
	if id1 != id2 || sid1 != sid2 {
		t.Fatalf("deterministic sign not stable: (%s,%s) vs (%s,%s)", id1, sid1, id2, sid2)
	}
}

func TestReleaseRegenerateMatchesFrozenSignedFixture(t *testing.T) {
	rcSigned := filepath.Join(pcsCoreRoot(t), "examples", "labtrust-release", "signed_science_claim_bundle.json")
	if _, err := os.Stat(rcSigned); err != nil {
		t.Skip("pcs-core labtrust-release signed fixture not available")
	}
	pfSigned := labtrustReleaseFixture(t, "signed_science_claim_bundle.json")
	if pfHash, err1 := fileSHA256Hex(pfSigned); err1 == nil {
		if rcHash, err2 := fileSHA256Hex(rcSigned); err2 == nil && pfHash == rcHash {
			frozen, err := pcs.LoadSignedScienceClaimBundle(pfSigned)
			if err != nil {
				t.Fatal(err)
			}
			if err := pcs.VerifySignedBundleIntegrity(frozen, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
				t.Fatal(err)
			}
			return
		}
	}

	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	t.Setenv("PF_DETERMINISTIC", "1")

	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := releaseModeValidateOpts(t)
	opts.RepoRoot = root
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	loaded, _ := pcs.LoadHandoff(validHandoffManifestPath(t))
	regenerated, err := pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: true,
		BundlePath:  path,
		Handoff:     loaded,
	})
	if err != nil {
		t.Fatal(err)
	}
	if os.Getenv("UPDATE_PCS_GOLDEN") == "1" {
		if err := writeJSONFixture(pfSigned, regenerated); err != nil {
			t.Fatal(err)
		}
		vrPath := labtrustReleaseFixture(t, "verification_result.json")
		if err := writeJSONFixture(vrPath, regenerated.VerificationResult); err != nil {
			t.Fatal(err)
		}
		t.Logf("updated golden fixtures signed_bundle_id=%s", regenerated.SignedBundleID)
		return
	}
	frozen, err := pcs.LoadSignedScienceClaimBundle(pfSigned)
	if err != nil {
		t.Fatal(err)
	}
	if regenerated.SignedBundleID != frozen.SignedBundleID {
		t.Fatalf("signed_bundle_id mismatch after regenerate: %q vs %q",
			regenerated.SignedBundleID, frozen.SignedBundleID)
	}
	if regenerated.SignatureOrDigest != frozen.SignatureOrDigest {
		t.Fatalf("wrapper digest mismatch after regenerate")
	}
}

func releaseDeterministicGoldenIDs(pfCommit string, t *testing.T) (verificationID, signedBundleID string) {
	t.Helper()
	t.Setenv("PF_SOURCE_COMMIT", pfCommit)
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := releaseModeValidateOpts(t)
	opts.RepoRoot = root
	opts.SourceCommit = pfCommit
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	loaded, _ := pcs.LoadHandoff(validHandoffManifestPath(t))
	signed, err := pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: true,
		BundlePath:  path,
		Handoff:     loaded,
	})
	if err != nil {
		t.Fatal(err)
	}
	return signed.VerificationResult.VerificationID, signed.SignedBundleID
}
