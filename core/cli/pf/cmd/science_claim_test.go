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
		if _, err := os.Stat(filepath.Join(dir, "tests", "pcs", "valid_labtrust_bundle.json")); err == nil {
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
	bundle := filepath.Join(repoRoot(t), "tests", "pcs", "valid_labtrust_bundle.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--json")
	cmd.Dir = pfDir(t)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("verify failed: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), `"status": "passed"`) {
		t.Fatalf("expected passed status in output: %s", out)
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

func TestInspectPrintsCheckSummaryCLI(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "valid_labtrust_bundle.json")
	signed := filepath.Join(t.TempDir(), "signed_science_claim_bundle.json")

	sign := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", signed)
	sign.Dir = pfDir(t)
	if out, err := sign.CombinedOutput(); err != nil {
		t.Fatalf("sign failed: %v\n%s", err, out)
	}

	inspect := exec.Command("go", "run", ".", "inspect", "science-claim", signed)
	inspect.Dir = pfDir(t)
	out, err := inspect.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	if !strings.Contains(body, "verification_status:  passed") && !strings.Contains(body, "verification_status: passed") {
		t.Fatalf("inspect output missing passed status:\n%s", body)
	}
	if !strings.Contains(body, "Checks (15):") {
		t.Fatalf("inspect must list all 15 checks:\n%s", body)
	}
	for _, id := range []string{"trace_hash_alignment", "science_claim_bundle_schema", "source_commit_not_placeholder"} {
		if !strings.Contains(body, id) {
			t.Fatalf("inspect missing check_id %s", id)
		}
	}
}
