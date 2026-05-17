// SPDX-License-Identifier: Apache-2.0

package pcs_test

import (
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestResolveArtifactPathFromCLIWorkingDirectory(t *testing.T) {
	root := repoRoot(t)
	pfDir := filepath.Join(root, "core", "cli", "pf")
	if err := os.Chdir(pfDir); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Chdir(root) })

	// Wrong depth (what users often type from core/cli/pf).
	_, err := os.Stat(filepath.Join(root, "core", "tests", "pcs", "valid_labtrust_bundle.json"))
	if err == nil {
		t.Fatal("expected core/tests/pcs not to exist")
	}

	resolved, err := pcs.ResolveArtifactPath("../../tests/pcs/valid_labtrust_bundle.json")
	if err != nil {
		t.Fatal(err)
	}
	want := filepath.Join(root, "tests", "pcs", "valid_labtrust_bundle.json")
	if filepath.Clean(resolved) != filepath.Clean(want) {
		t.Fatalf("got %s want %s", resolved, want)
	}
}

func TestResolveArtifactPathPrefersRepoRootTestsPCS(t *testing.T) {
	root := repoRoot(t)
	pfDir := filepath.Join(root, "core", "cli", "pf")
	shadowDir := filepath.Join(pfDir, "tests", "pcs")
	if err := os.MkdirAll(shadowDir, 0755); err != nil {
		t.Fatal(err)
	}
	shadow := filepath.Join(shadowDir, "_shadow_bundle.json")
	if err := os.WriteFile(shadow, []byte(`{"shadow":true}`), 0644); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Remove(shadow) })

	canonical := filepath.Join(root, "tests", "pcs", "valid_labtrust_bundle.json")
	if err := os.Chdir(pfDir); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Chdir(root) })

	resolved, err := pcs.ResolveArtifactPath("tests/pcs/valid_labtrust_bundle.json")
	if err != nil {
		t.Fatal(err)
	}
	if filepath.Clean(resolved) != filepath.Clean(canonical) {
		t.Fatalf("got %s want %s", resolved, canonical)
	}
}

func TestResolveOutputPathTestsPCSFromCLI(t *testing.T) {
	root := repoRoot(t)
	pfDir := filepath.Join(root, "core", "cli", "pf")
	if err := os.Chdir(pfDir); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Chdir(root) })

	out := filepath.Join(root, "tests", "pcs", "_resolve_output_path_test.json")
	t.Cleanup(func() { _ = os.Remove(out) })

	resolved, err := pcs.ResolveOutputPath("tests/pcs/_resolve_output_path_test.json")
	if err != nil {
		t.Fatal(err)
	}
	if filepath.Clean(resolved) != filepath.Clean(out) {
		t.Fatalf("got %s want %s", resolved, out)
	}
}

func TestResolveArtifactPathShortName(t *testing.T) {
	root := repoRoot(t)
	pfDir := filepath.Join(root, "core", "cli", "pf")
	_ = os.Chdir(pfDir)
	t.Cleanup(func() { _ = os.Chdir(root) })

	resolved, err := pcs.ResolveArtifactPath("tests/pcs/valid_labtrust_bundle.json")
	if err != nil {
		t.Fatal(err)
	}
	if filepath.Base(resolved) != "valid_labtrust_bundle.json" {
		t.Fatalf("unexpected %s", resolved)
	}
}
