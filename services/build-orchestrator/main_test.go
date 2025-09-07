package main

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

func TestArtifactHashingAndIntegrity(t *testing.T) {
	orchestrator := NewBuildOrchestrator()
	build := PolicyBuild{
		BuildID: "test-build",
		CompiledDFA: CompiledDFA{
			States:       []DFAState{{StateID: 0, Name: "initial", Type: "initial"}},
			Transitions:  []DFATransition{},
			InitialState: 0,
			AcceptStates: []int{},
			RejectStates: []int{},
			Metadata:     map[string]string{"compiler": "test"},
		},
		Labeler: LabelerConfig{Labels: []Label{{Name: "public", Level: 0}}},
	}

	artifacts, index, err := orchestrator.generateBuildArtifacts(&build)
	if err != nil {
		t.Fatalf("generateBuildArtifacts failed: %v", err)
	}
	if len(artifacts) == 0 || len(index) == 0 {
		t.Fatalf("expected artifacts and index, got none")
	}

	for _, meta := range index {
		if meta.Sha256 == "" || meta.Size <= 0 {
			t.Fatalf("invalid meta for %s: sha=%s size=%d", meta.Name, meta.Sha256, meta.Size)
		}
		data, err := os.ReadFile(meta.Path)
		if err != nil {
			t.Fatalf("failed to read artifact %s: %v", meta.Path, err)
		}
		h := sha256.Sum256(data)
		if fmt.Sprintf("%x", h) != meta.Sha256 {
			t.Fatalf("hash mismatch for %s", meta.Name)
		}
	}

	manifestPath := filepath.Join(orchestrator.cachePath, build.BuildID, "build_manifest.json")
	b, err := os.ReadFile(manifestPath)
	if err != nil {
		t.Fatalf("failed to read manifest: %v", err)
	}
	var manifest PolicyBuild
	if err := json.Unmarshal(b, &manifest); err != nil {
		t.Fatalf("invalid manifest JSON: %v", err)
	}
}
