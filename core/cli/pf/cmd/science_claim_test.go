// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func repoRoot(t *testing.T) string {
	t.Helper()
	wd, _ := os.Getwd()
	dir := wd
	for {
		if _, err := os.Stat(filepath.Join(dir, "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("repo root not found")
		}
		dir = parent
	}
}

func pfDir(t *testing.T) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "core", "cli", "pf")
}

func TestVerifyValidLabtrustBundlePassesCLI(t *testing.T) {
	bundle := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--json")
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("verify failed: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), `"status": "ProofChecked"`) {
		t.Fatalf("expected ProofChecked status in output: %s", out)
	}
	if !strings.Contains(string(out), `"schema_version": "v0"`) {
		t.Fatalf("expected schema_version v0: %s", out)
	}
}

func TestSignFailedBundleRefusesCLI(t *testing.T) {
	bundle := filepath.Join(repoRoot(t), "tests", "pcs", "invalid_missing_certificate.json")
	cmd := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", filepath.Join(t.TempDir(), "signed.json"))
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected sign to fail, got success: %s", out)
	}
	if !strings.Contains(string(out), "signing refused") {
		t.Fatalf("expected signing refused message: %s", out)
	}
}

func TestVerifyLegacySingularRuntimeReceiptFailsCLI(t *testing.T) {
	bundle := filepath.Join(repoRoot(t), "tests", "pcs", "invalid_legacy_singular_runtime_receipt.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle)
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected legacy verify to fail: %s", out)
	}
	if !strings.Contains(string(out), "legacy pcs bundle format") {
		t.Fatalf("expected legacy error, got: %s", out)
	}
}

func TestMigrateLegacyBundleCLI(t *testing.T) {
	legacy := filepath.Join(repoRoot(t), "tests", "pcs", "invalid_legacy_singular_runtime_receipt.json")
	out := filepath.Join(t.TempDir(), "migrated.json")
	cmd := exec.Command("go", "run", ".", "migrate", "science-claim", legacy, "--out", out)
	cmd.Dir = pfDir(t)
	if outBytes, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("migrate failed: %v\n%s", err, outBytes)
	}
	verify := exec.Command("go", "run", ".", "verify", "science-claim", out, "--json")
	verify.Dir = pfDir(t)
	verifyOut, err := verify.CombinedOutput()
	if err != nil {
		t.Fatalf("verify migrated bundle failed: %v\n%s", err, verifyOut)
	}
	if !strings.Contains(string(verifyOut), `"status": "ProofChecked"`) {
		t.Fatalf("expected ProofChecked after migration: %s", verifyOut)
	}
}

func TestInspectReverifyFailureExitsNonZeroCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")
	signed := filepath.Join(t.TempDir(), "signed_corrupt.json")

	sign := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", signed)
	sign.Dir = pfDir(t)
	if out, err := sign.CombinedOutput(); err != nil {
		t.Fatalf("sign failed: %v\n%s", err, out)
	}

	raw, err := os.ReadFile(signed)
	if err != nil {
		t.Fatal(err)
	}
	corrupt := strings.Replace(string(raw),
		"sha256:5555555555555555555555555555555555555555555555555555555555555555",
		"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
		1)
	if err := os.WriteFile(signed, []byte(corrupt), 0644); err != nil {
		t.Fatal(err)
	}

	inspect := exec.Command("go", "run", ".", "inspect", "science-claim", signed, "--reverify")
	inspect.Dir = pfDir(t)
	out, err := inspect.CombinedOutput()
	if err == nil {
		t.Fatalf("expected inspect --reverify to fail on corrupted bundle: %s", out)
	}
	if !strings.Contains(string(out), "reverification failed") {
		t.Fatalf("expected reverification failed message: %s", out)
	}
}

func TestPFReleaseModeRejectsPlaceholderCommitCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release", "science_claim_bundle.certified.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = append(os.Environ(),
		"PF_SOURCE_COMMIT=cccccccccccccccccccccccccccccccccccccccc",
		"PF_RELEASE_MODE=0",
	)
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected verify --release-mode to fail with placeholder commit: %s", out)
	}
	if !strings.Contains(string(out), "placeholder") && !strings.Contains(string(out), "release-mode") {
		t.Fatalf("expected release-mode provenance error: %s", out)
	}
}

func TestValidateLabtrustReleaseArtifactsCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	for _, args := range [][]string{
		{"validate", "verification-result", filepath.Join(release, "verification_result.json")},
		{"validate", "signed-science-claim", filepath.Join(release, "signed_science_claim_bundle.json")},
	} {
		cmd := exec.Command("go", append([]string{"run", "."}, args...)...)
		cmd.Dir = pfDir(t)
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("%v failed: %v\n%s", args, err, out)
		}
		if !strings.Contains(string(out), "OK:") {
			t.Fatalf("expected OK from validate %v: %s", args, out)
		}
	}
}

func TestInspectLabtrustReleaseSignedBundleCLI(t *testing.T) {
	signed := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust-release", "signed_science_claim_bundle.json")
	cmd := exec.Command("go", "run", ".", "inspect", "science-claim", signed, "--strict")
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "verification_status:  ProofChecked") {
		t.Fatalf("expected ProofChecked verification_status:\n%s", body)
	}
	if !strings.Contains(body, "Embedded checks (15):") {
		t.Fatalf("expected 15 embedded checks:\n%s", body)
	}
	if !strings.Contains(body, "scb-pcs-qc-release-v0.1") {
		t.Fatalf("expected release bundle_id in inspect output:\n%s", body)
	}
}

func TestInspectRejectsTamperedReleaseSignedBundleCLI(t *testing.T) {
	src := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust-release", "signed_science_claim_bundle.json")
	tampered := filepath.Join(t.TempDir(), "signed_tampered.json")
	raw, err := os.ReadFile(src)
	if err != nil {
		t.Fatal(err)
	}
	corrupt := strings.Replace(string(raw),
		`"signature_or_digest": "sha256:`,
		`"signature_or_digest": "sha256:0000000000000000000000000000000000000000000000000000000000000000`,
		1)
	if err := os.WriteFile(tampered, []byte(corrupt), 0644); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "run", ".", "inspect", "science-claim", tampered, "--strict")
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected inspect --strict to fail on tampered signed bundle: %s", out)
	}
	if !strings.Contains(string(out), "integrity") && !strings.Contains(string(out), "digest") {
		t.Fatalf("expected digest/integrity error: %s", out)
	}
}

func TestInspectLabtrustSignedBundleCLI(t *testing.T) {
	signed := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust", "signed_science_claim_bundle.labtrust-export.json")
	cmd := exec.Command("go", "run", ".", "inspect", "science-claim", signed, "--reverify")
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "PF re-verification (15):") {
		t.Fatalf("expected 15 PF re-verification checks:\n%s", body)
	}
	if !strings.Contains(body, "pf_status:            ProofChecked") {
		t.Fatalf("expected ProofChecked pf_status:\n%s", body)
	}
}

func TestInspectPrintsCheckSummaryCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")
	signed := filepath.Join(t.TempDir(), "signed_science_claim_bundle.json")

	sign := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", signed)
	sign.Dir = pfDir(t)
	if out, err := sign.CombinedOutput(); err != nil {
		t.Fatalf("sign failed: %v\n%s", err, out)
	}

	inspect := exec.Command("go", "run", ".", "inspect", "science-claim", signed, "--strict")
	inspect.Dir = pfDir(t)
	out, err := inspect.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "verification_status:  ProofChecked") && !strings.Contains(body, "verification_status: ProofChecked") {
		t.Fatalf("inspect output missing ProofChecked status:\n%s", body)
	}
	if !strings.Contains(body, "Embedded checks (15):") {
		t.Fatalf("inspect must list all 15 embedded checks:\n%s", body)
	}
	for _, id := range []string{"trace_hash_alignment", "science_claim_bundle_schema", "source_commit_not_placeholder"} {
		if !strings.Contains(body, id) {
			t.Fatalf("inspect missing check_id %s", id)
		}
	}
}
