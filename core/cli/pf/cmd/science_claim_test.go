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

func TestCLIVerifyScienceClaim(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "valid_labtrust_bundle.json")
	cmd := exec.Command("go", "run", ".", "verify", "science-claim", bundle, "--json")
	cmd.Dir = filepath.Join(root, "core", "cli", "pf")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("verify failed: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), `"status": "passed"`) {
		t.Fatalf("expected passed status in output: %s", out)
	}
}

func TestCLIInspectScienceClaim(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "valid_labtrust_bundle.json")
	pfDir := filepath.Join(root, "core", "cli", "pf")
	signed := filepath.Join(t.TempDir(), "signed_science_claim_bundle.json")

	sign := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", signed)
	sign.Dir = pfDir
	if out, err := sign.CombinedOutput(); err != nil {
		t.Fatalf("sign failed: %v\n%s", err, out)
	}

	inspect := exec.Command("go", "run", ".", "inspect", "science-claim", signed)
	inspect.Dir = pfDir
	out, err := inspect.CombinedOutput()
	if err != nil {
		t.Fatalf("inspect failed: %v\n%s", err, out)
	}
	body := string(out)
	for _, want := range []string{"verification_status: passed", "pcs.schema.science_claim_bundle", "Checks (14):"} {
		if !strings.Contains(body, want) {
			t.Fatalf("inspect output missing %q:\n%s", want, body)
		}
	}
	for _, id := range []string{
		"pcs.presence.claim_artifact",
		"pcs.metadata.signature_or_digest",
	} {
		if !strings.Contains(body, id) {
			t.Fatalf("inspect output missing check %q", id)
		}
	}
}

func TestCLISignRejectsFailedBundle(t *testing.T) {
	root := repoRoot(t)
	bundle := filepath.Join(root, "tests", "pcs", "invalid_missing_certificate.json")
	cmd := exec.Command("go", "run", ".", "sign", "science-claim", bundle, "--out", filepath.Join(t.TempDir(), "signed.json"))
	cmd.Dir = filepath.Join(root, "core", "cli", "pf")
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("expected sign to fail, got success: %s", out)
	}
	if !strings.Contains(string(out), "signing refused") {
		t.Fatalf("expected signing refused message: %s", out)
	}
}
