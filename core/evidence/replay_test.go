// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"path/filepath"
	"testing"
)

func TestReplayValidFixture(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid", "basic-evidence-bundle.json")
	out := filepath.Join(t.TempDir(), "replay-report.json")
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		OutPath:    out,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
	})
	if err != nil {
		t.Fatalf("replay: %v (%v)", err, report.Errors)
	}
	if !report.TraceFound {
		t.Fatal("expected execution trace in fixture bundle")
	}
}

func TestReplayTamperedDigestFails(t *testing.T) {
	root := repoRoot(t)
	bad := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "invalid", "bad-bundle-digest.json")
	_, err := ReplayBundle(ReplayOptions{
		BundlePath: bad,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bad),
	})
	if err == nil {
		t.Fatal("expected replay failure for tampered bundle")
	}
}
