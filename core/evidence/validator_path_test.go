// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"os"
	"path/filepath"
	"testing"
)

func TestResolveContainedExistingPathAcceptsContainedRelativeFile(t *testing.T) {
	base := t.TempDir()
	path := filepath.Join(base, "artifacts", "claim.json")
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	resolved, err := resolveContainedExistingPath(base, "artifacts/claim.json")
	if err != nil {
		t.Fatalf("expected contained path to resolve: %v", err)
	}
	expected, err := filepath.EvalSymlinks(path)
	if err != nil {
		t.Fatal(err)
	}
	if resolved != expected {
		t.Fatalf("resolved path mismatch: expected %q got %q", expected, resolved)
	}
}

func TestResolveContainedExistingPathAcceptsContainedAbsoluteFile(t *testing.T) {
	base := t.TempDir()
	path := filepath.Join(base, "trace.json")
	if err := os.WriteFile(path, []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	if _, err := resolveContainedExistingPath(base, path); err != nil {
		t.Fatalf("expected contained absolute path to resolve: %v", err)
	}
}

func TestResolveContainedExistingPathRejectsTraversal(t *testing.T) {
	root := t.TempDir()
	base := filepath.Join(root, "base")
	if err := os.MkdirAll(base, 0755); err != nil {
		t.Fatal(err)
	}
	outside := filepath.Join(root, "outside.json")
	if err := os.WriteFile(outside, []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	if _, err := resolveContainedExistingPath(base, "../outside.json"); err == nil {
		t.Fatal("expected traversal outside base to fail")
	}
}

func TestResolveContainedExistingPathRejectsFileSymlinkEscape(t *testing.T) {
	root := t.TempDir()
	base := filepath.Join(root, "base")
	if err := os.MkdirAll(base, 0755); err != nil {
		t.Fatal(err)
	}
	outside := filepath.Join(root, "outside.json")
	if err := os.WriteFile(outside, []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	link := filepath.Join(base, "linked.json")
	if err := os.Symlink(outside, link); err != nil {
		t.Skipf("symlink unavailable: %v", err)
	}
	if _, err := resolveContainedExistingPath(base, "linked.json"); err == nil {
		t.Fatal("expected file symlink escape to fail")
	}
}

func TestResolveContainedExistingPathRejectsDirectorySymlinkEscape(t *testing.T) {
	root := t.TempDir()
	base := filepath.Join(root, "base")
	outside := filepath.Join(root, "outside")
	if err := os.MkdirAll(base, 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(outside, 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(outside, "env.json"), []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outside, filepath.Join(base, "fixtures")); err != nil {
		t.Skipf("symlink unavailable: %v", err)
	}
	if _, err := resolveContainedExistingPath(base, "fixtures/env.json"); err == nil {
		t.Fatal("expected directory symlink escape to fail")
	}
}
