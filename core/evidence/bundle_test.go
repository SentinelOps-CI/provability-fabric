// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

func repoRoot(t *testing.T) string {
	t.Helper()
	root, err := FindRepoRoot(".")
	if err != nil {
		t.Fatalf("find repo root: %v", err)
	}
	return root
}

func TestPackDeepReplayFixtureMatchesCheckedIn(t *testing.T) {
	root := repoRoot(t)
	exampleDir := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid")
	out := filepath.Join(t.TempDir(), "deep-replay-bundle.json")
	if _, err := Pack(PackOptions{
		ManifestPath: filepath.Join(exampleDir, "manifest.json"),
		OutPath:      out,
		BaseDir:      exampleDir,
	}); err != nil {
		t.Fatalf("pack: %v", err)
	}
	got, err := os.ReadFile(out)
	if err != nil {
		t.Fatal(err)
	}
	want, err := os.ReadFile(filepath.Join(exampleDir, "deep-replay-bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != string(want) {
		t.Fatalf("checked-in deep-replay-bundle.json is stale\n--- packed ---\n%s", got)
	}
}

func TestPackValidFixture(t *testing.T) {
	root := repoRoot(t)
	exampleDir := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid")
	manifest := filepath.Join(exampleDir, "manifest.json")
	out := filepath.Join(t.TempDir(), "bundle.json")

	bundle, err := Pack(PackOptions{
		ManifestPath: manifest,
		OutPath:      out,
		BaseDir:      exampleDir,
	})
	if err != nil {
		t.Fatalf("pack: %v", err)
	}
	if bundle.BundleDigest == "" {
		t.Fatal("expected bundle_digest")
	}
}

func TestValidateFixtureBundle(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid", "basic-evidence-bundle.json")
	_, err := ValidateBundle(ValidateOptions{
		BundlePath: bundlePath,
		Strict:     true,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
	})
	if err != nil {
		t.Fatalf("validate fixture: %v", err)
	}
}

func TestBundleDigestDeterministic(t *testing.T) {
	root := repoRoot(t)
	exampleDir := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid")
	manifest := filepath.Join(exampleDir, "manifest.json")
	tmp := t.TempDir()
	out1 := filepath.Join(tmp, "one.json")
	out2 := filepath.Join(tmp, "two.json")

	b1, err := Pack(PackOptions{ManifestPath: manifest, OutPath: out1, BaseDir: exampleDir})
	if err != nil {
		t.Fatalf("pack one: %v", err)
	}
	b2, err := Pack(PackOptions{ManifestPath: manifest, OutPath: out2, BaseDir: exampleDir})
	if err != nil {
		t.Fatalf("pack two: %v", err)
	}
	if b1.BundleDigest != b2.BundleDigest {
		t.Fatalf("digests differ: %s vs %s", b1.BundleDigest, b2.BundleDigest)
	}
}

func TestBundleToMapRoundTrip(t *testing.T) {
	bundle := EvidenceBundle{
		BundleID:      "test",
		SchemaVersion: SchemaVersion,
		CreatedAt:     "2025-01-01T00:00:00Z",
		Producer:      "test",
		Artifacts: []ArtifactRef{{
			Role: "claim", Path: "artifacts/claim.json",
			MediaType: "application/vnd.provability-fabric.evidence.claim+json",
			Digest:    "sha256:abc",
		}},
	}
	m, err := bundleToMap(bundle)
	if err != nil {
		t.Fatalf("bundleToMap: %v", err)
	}
	if _, ok := m["artifacts"].([]any); !ok {
		raw, _ := json.Marshal(m["artifacts"])
		t.Fatalf("artifacts not []any: %s", string(raw))
	}
}

func TestMissingArtifactFails(t *testing.T) {
	root := repoRoot(t)
	bad := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "invalid", "missing-artifacts.json")
	_, err := ValidateBundle(ValidateOptions{
		BundlePath: bad,
		Strict:     true,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bad),
	})
	if err == nil {
		t.Fatal("expected validation failure")
	}
}

func TestCanonicalJSONDigest(t *testing.T) {
	left := map[string]any{"b": 1, "a": 2}
	right := map[string]any{"a": 2, "b": 1}
	d1, err := CanonicalJSONDigest(left, "")
	if err != nil {
		t.Fatal(err)
	}
	d2, err := CanonicalJSONDigest(right, "")
	if err != nil {
		t.Fatal(err)
	}
	if d1 != d2 {
		t.Fatalf("canonical digests differ: %s %s", d1, d2)
	}
}

func TestFileDigest(t *testing.T) {
	f := filepath.Join(t.TempDir(), "x.txt")
	if err := os.WriteFile(f, []byte("hello"), 0644); err != nil {
		t.Fatal(err)
	}
	d, err := FileDigest(f)
	if err != nil {
		t.Fatal(err)
	}
	if d != "sha256:2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824" {
		t.Fatalf("unexpected digest %s", d)
	}
}
