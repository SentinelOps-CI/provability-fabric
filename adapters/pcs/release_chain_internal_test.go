// SPDX-License-Identifier: Apache-2.0
package pcs

import (
	"os"
	"path/filepath"
	"testing"
)

func TestRunReleaseChainChecksIncludesRegistrySemantic(t *testing.T) {
	root := repoRootForTest(t)
	artifactDir := filepath.Join(root, "..", "pcs-core", "examples", "labtrust-release")
	if _, err := os.Stat(filepath.Join(artifactDir, "trace.json")); err != nil {
		t.Skip("pcs-core labtrust-release required")
	}
	manifestPath := filepath.Join(artifactDir, "release_manifest.v0.json")
	manifest, err := LoadReleaseManifest(manifestPath)
	if err != nil {
		t.Fatal(err)
	}
	registryPath := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release", "artifact_registry.json")
	registry, err := LoadArtifactRegistry(registryPath)
	if err != nil {
		t.Fatal(err)
	}
	checks, _ := runReleaseChainChecks(artifactDir, manifest, ReleaseChainVerifyOptions{
		RepoRoot:    root,
		ArtifactDir: artifactDir,
		Registry:    registry,
		ReleaseMode: true,
	})
	var registryN int
	for _, c := range checks {
		if len(c.CheckID) > 9 && c.CheckID[:9] == "registry." {
			registryN++
		}
	}
	t.Logf("runReleaseChainChecks total=%d registry=%d", len(checks), registryN)
	if registryN == 0 {
		t.Fatal("expected registry semantic checks from runReleaseChainChecks")
	}
}

func repoRootForTest(t *testing.T) string {
	t.Helper()
	dir, _ := os.Getwd()
	for {
		if _, err := os.Stat(filepath.Join(dir, "tests", "pcs", "fixtures")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("repo root not found")
		}
		dir = parent
	}
}
