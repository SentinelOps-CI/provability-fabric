// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd_test

import (
	"encoding/json"
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

// pfCLIEnv clears PF_RELEASE_MODE from the parent environment so local dev shells
// do not turn every verify/sign into release-mode admission.
func pfCLIEnv(extra ...string) []string {
	env := make([]string, 0, len(os.Environ())+1+len(extra))
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "PF_RELEASE_MODE=") {
			continue
		}
		env = append(env, e)
	}
	env = append(env, "PF_RELEASE_MODE=0")
	return append(env, extra...)
}

func pfReleaseEnv(extra ...string) []string {
	env := make([]string, 0, len(os.Environ())+1+len(extra))
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "PF_RELEASE_MODE=") || strings.HasPrefix(e, "PF_ADMISSION_PROFILE=") {
			continue
		}
		env = append(env, e)
	}
	return append(append(env, "PF_RELEASE_MODE=1"), extra...)
}

func refreshReleaseManifestPins(t *testing.T, root, artifactDir string) {
	t.Helper()
	script := filepath.Join(root, "scripts", "refresh-release-manifest-pins.py")
	try := func(name string, args ...string) error {
		cmd := exec.Command(name, args...)
		cmd.Dir = root
		_, err := cmd.CombinedOutput()
		return err
	}
	for _, spec := range []struct {
		name string
		args []string
	}{
		{"python3", []string{script, artifactDir}},
		{"python", []string{script, artifactDir}},
		{"py", []string{"-3", script, artifactDir}},
	} {
		if _, err := exec.LookPath(spec.name); err != nil {
			continue
		}
		if err := try(spec.name, spec.args...); err == nil {
			return
		}
	}
	t.Fatalf("refresh manifest pins: no working python (tried python3, python, py -3)")
}

func TestVerifyValidLabtrustBundlePassesCLI(t *testing.T) {
	bundle := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--json")
	cmd.Dir = pfDir(t)
	cmd.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv()
	if outBytes, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("migrate failed: %v\n%s", err, outBytes)
	}
	verify := exec.Command("go", "run", ".", "verify", "science-claim", out, "--json")
	verify.Dir = pfDir(t)
	verify.Env = pfCLIEnv()
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
	sign.Env = pfCLIEnv()
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
	inspect.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv("PF_SOURCE_COMMIT=cccccccccccccccccccccccccccccccccccccccc")
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
		{"validate", "handoff-manifest", filepath.Join(release, "handoff_to_pf.json")},
		{"validate", "release-manifest", filepath.Join(release, "release_manifest.json")},
		{"validate", "artifact-registry", filepath.Join(release, "artifact_registry.json")},
		{"validate", "release-chain-result", filepath.Join(release, "release_chain_validation_result.json")},
	} {
		cmd := exec.Command("go", append([]string{"run", "."}, args...)...)
		cmd.Dir = pfDir(t)
		cmd.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv()
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "verification_status:  ProofChecked") {
		t.Fatalf("expected ProofChecked verification_status:\n%s", body)
	}
	if !strings.Contains(body, "Embedded checks (15):") && !strings.Contains(body, "Embedded checks (17):") {
		t.Fatalf("expected embedded checks summary:\n%s", body)
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
	cmd.Env = pfCLIEnv()
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
	cmd.Env = pfCLIEnv()
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "PF re-verification (15):") && !strings.Contains(body, "PF re-verification (17):") {
		t.Fatalf("expected PF re-verification checks:\n%s", body)
	}
	if !strings.Contains(body, "pf_status:            ProofChecked") {
		t.Fatalf("expected ProofChecked pf_status:\n%s", body)
	}
}

func TestVerifyScienceClaimWithHandoffManifestCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	bundle := filepath.Join(release, "science_claim_bundle.certified.json")
	handoff := filepath.Join(release, "handoff_to_pf.json")
	manifestPath := filepath.Join(release, "FIXTURE_MANIFEST.json")
	manifestBytes, err := os.ReadFile(manifestPath)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(manifestBytes), "pf_source_commit") {
		t.Fatal("fixture manifest missing pf_source_commit")
	}
	registry := filepath.Join(release, "artifact_registry.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle,
		"--handoff", handoff, "--registry", registry, "--admission-profile", "labtrust_qc_release", "--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv("PF_SOURCE_COMMIT=0f659b90c80c46a6bbfd51b0d37ea723b032fb9d", "PCS_CORE_PATH="+filepath.Join(root, "..", "pcs-core"))
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("verify with handoff failed: %v\n%s", err, out)
	}
}

func TestVerifyScienceClaimWithHandoffAndRegistryCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	bundle := filepath.Join(release, "science_claim_bundle.certified.json")
	handoff := filepath.Join(release, "handoff_to_pf.json")
	registry := filepath.Join(release, "artifact_registry.json")
	if _, err := os.Stat(registry); err != nil {
		t.Skip("artifact registry fixture not present")
	}
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle,
		"--handoff", handoff,
		"--registry", registry,
		"--admission-profile", "labtrust_qc_release",
		"--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv("PF_SOURCE_COMMIT=0f659b90c80c46a6bbfd51b0d37ea723b032fb9d")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("verify with handoff+registry failed: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), "ProofChecked") {
		t.Fatalf("expected ProofChecked: %s", out)
	}
}

func TestVerifyReleaseChainCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	manifest := filepath.Join(release, "release_manifest.json")
	artifactDir := release
	pcsCore := filepath.Join(root, "..", "pcs-core", "examples", "labtrust-release")
	if _, err := os.Stat(filepath.Join(pcsCore, "science_claim_bundle.certified.json")); err == nil {
		artifactDir = pcsCore
		if _, err := os.Stat(filepath.Join(pcsCore, "release_manifest.v0.json")); err == nil {
			manifest = filepath.Join(pcsCore, "release_manifest.v0.json")
		}
	} else if _, err := os.Stat(manifest); err != nil {
		t.Skip("release manifest fixtures not present")
	}
	pfCommit := "0f659b90c80c46a6bbfd51b0d37ea723b032fb9d"
	if raw, err := os.ReadFile(filepath.Join(release, "FIXTURE_MANIFEST.json")); err == nil {
		var fm struct {
			PFSourceCommit string `json:"pf_source_commit"`
		}
		if json.Unmarshal(raw, &fm) == nil && fm.PFSourceCommit != "" {
			pfCommit = fm.PFSourceCommit
		}
	}
	refreshReleaseManifestPins(t, root, artifactDir)
	outPath := filepath.Join(t.TempDir(), "release_chain_validation_result.json")
	registry := filepath.Join(release, "artifact_registry.json")
	cmd := exec.Command("go", "run", ".", "verify", "release-chain",
		"--manifest", manifest,
		"--registry", registry,
		"--artifact-dir", artifactDir,
		"--out", outPath,
		"--admission-profile", "labtrust_qc_release",
		"--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv("PF_SOURCE_COMMIT=" + pfCommit)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("verify release-chain failed: %v\n%s", err, out)
	}
	data, err := os.ReadFile(outPath)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(data), `"status": "ProofChecked"`) {
		t.Fatalf("expected ProofChecked release chain result: %s", data)
	}
}

func TestInspectPrintsCheckSummaryCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust", "science_claim_bundle.certified.json")
	signed := filepath.Join(t.TempDir(), "signed_science_claim_bundle.json")

	sign := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", signed)
	sign.Dir = pfDir(t)
	sign.Env = pfCLIEnv()
	if out, err := sign.CombinedOutput(); err != nil {
		t.Fatalf("sign failed: %v\n%s", err, out)
	}

	inspect := exec.Command("go", "run", ".", "inspect", "science-claim", signed, "--strict")
	inspect.Dir = pfDir(t)
	inspect.Env = pfCLIEnv()
	out, err := inspect.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "verification_status:  ProofChecked") && !strings.Contains(body, "verification_status: ProofChecked") {
		t.Fatalf("inspect output missing ProofChecked status:\n%s", body)
	}
	if !strings.Contains(body, "Embedded checks (17):") {
		t.Fatalf("inspect must list all 17 embedded checks:\n%s", body)
	}
	for _, id := range []string{"trace_hash_alignment", "science_claim_bundle_schema", "source_commit_not_placeholder", "status_transition_policy"} {
		if !strings.Contains(body, id) {
			t.Fatalf("inspect missing check_id %s", id)
		}
	}
}

func TestReleaseModeRequiresHandoffCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	bundle := filepath.Join(release, "science_claim_bundle.certified.json")
	registry := filepath.Join(release, "artifact_registry.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle,
		"--registry", registry, "--admission-profile", "labtrust_qc_release", "--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv("PF_SOURCE_COMMIT=0f659b90c80c46a6bbfd51b0d37ea723b032fb9d")
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected release-mode without handoff to fail: %s", out)
	}
	if !strings.Contains(string(out), "handoff") {
		t.Fatalf("expected handoff requirement in output: %s", out)
	}
}

func TestReleaseModeRequiresAdmissionProfileCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	bundle := filepath.Join(release, "science_claim_bundle.certified.json")
	handoff := filepath.Join(release, "handoff_to_pf.json")
	registry := filepath.Join(release, "artifact_registry.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle,
		"--handoff", handoff, "--registry", registry, "--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv("PF_SOURCE_COMMIT=0f659b90c80c46a6bbfd51b0d37ea723b032fb9d")
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected release-mode without admission profile to fail: %s", out)
	}
	if !strings.Contains(string(out), "missing_admission_profile") {
		t.Fatalf("expected missing_admission_profile in output: %s", out)
	}
}

func TestReleaseModeRequiresRegistryCLI(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	bundle := filepath.Join(release, "science_claim_bundle.certified.json")
	handoff := filepath.Join(release, "handoff_to_pf.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle,
		"--handoff", handoff, "--admission-profile", "labtrust_qc_release", "--release-mode")
	cmd.Dir = pfDir(t)
	cmd.Env = pfReleaseEnv(
		"PF_SOURCE_COMMIT=0f659b90c80c46a6bbfd51b0d37ea723b032fb9d",
		"PCS_CORE_PATH=",
	)
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected release-mode without registry to fail: %s", out)
	}
	if !strings.Contains(string(out), "registry") {
		t.Fatalf("expected registry requirement in output: %s", out)
	}
}

func TestExplainFailureCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release", "invalid_mismatched_trace_hash.json")
	vrPath := filepath.Join(t.TempDir(), "verification_result.json")
	verify := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--out", vrPath)
	verify.Dir = pfDir(t)
	verify.Env = pfCLIEnv()
	out, err := verify.CombinedOutput()
	if _, statErr := os.Stat(vrPath); statErr != nil {
		t.Fatalf("verify invalid bundle: %v\n%s", err, out)
	}
	if err == nil {
		t.Fatalf("expected verify to reject invalid bundle: %s", out)
	}
	explain := exec.Command("go", "run", ".", "explain", "failure", vrPath)
	explain.Dir = pfDir(t)
	out, err = explain.CombinedOutput()
	if err == nil {
		t.Fatalf("expected explain failure to exit non-zero: %s", out)
	}
	if !strings.Contains(string(out), "Repair") && !strings.Contains(string(out), "repair:") {
		t.Fatalf("expected repair hint in explain output: %s", out)
	}
}
