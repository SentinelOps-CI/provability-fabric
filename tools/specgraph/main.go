package main

import (
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/spf13/cobra"
	"gopkg.in/yaml.v3"
)

type SpecDependency struct {
	ID       string   `json:"id"`
	Requires []string `json:"requires,omitempty"`
	Path     string   `json:"path"`
}

type DependencyGraph struct {
	Specs []SpecDependency    `json:"specs"`
	Edges map[string][]string `json:"edges"`
}

type ImpactResult struct {
	ImpactedBundles []string `json:"impacted_bundles"`
	Cycles          []string `json:"cycles,omitempty"`
}

func main() {
	var rootCmd = &cobra.Command{
		Use:   "specgraph",
		Short: "Manage spec dependencies and detect impacted bundles",
	}

	var initCmd = &cobra.Command{
		Use:   "mod init",
		Short: "Initialize dependency graph from bundles",
		RunE:  runInit,
	}

	var impactCmd = &cobra.Command{
		Use:   "impact [changed-files]",
		Short: "Detect impacted bundles from changed files",
		Args:  cobra.MinimumNArgs(1),
		RunE:  runImpact,
	}

	rootCmd.AddCommand(initCmd, impactCmd)
	rootCmd.Execute()
}

func runInit(cmd *cobra.Command, args []string) error {
	graph, err := buildDependencyGraph()
	if err != nil {
		return fmt.Errorf("failed to build dependency graph: %w", err)
	}

	// Detect cycles
	cycles := detectCycles(graph)
	if len(cycles) > 0 {
		return fmt.Errorf("dependency cycles detected: %v", cycles)
	}

	// Write to spec-deps.json
	data, err := json.MarshalIndent(graph, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal graph: %w", err)
	}

	err = os.WriteFile("spec-deps.json", data, 0644)
	if err != nil {
		return fmt.Errorf("failed to write spec-deps.json: %w", err)
	}

	fmt.Println("✅ Dependency graph written to spec-deps.json")
	return nil
}

func runImpact(cmd *cobra.Command, args []string) error {
	// Load existing dependency graph
	data, err := os.ReadFile("spec-deps.json")
	if err != nil {
		return fmt.Errorf("failed to read spec-deps.json: %w", err)
	}

	var graph DependencyGraph
	err = json.Unmarshal(data, &graph)
	if err != nil {
		return fmt.Errorf("failed to parse spec-deps.json: %w", err)
	}

	// Find impacted bundles
	impacted := findImpactedBundles(graph, args)

	result := ImpactResult{
		ImpactedBundles: impacted,
	}

	// Output as JSON
	output, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal result: %w", err)
	}

	fmt.Println(string(output))
	return nil
}

func buildDependencyGraph() (*DependencyGraph, error) {
	graph := &DependencyGraph{
		Specs: []SpecDependency{},
		Edges: make(map[string][]string),
	}

	// Walk bundles directory
	err := filepath.WalkDir("bundles", func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}

		if d.IsDir() || !strings.HasSuffix(path, "spec.yaml") {
			return nil
		}

		// Read spec.yaml
		data, err := os.ReadFile(path)
		if err != nil {
			return fmt.Errorf("failed to read %s: %w", path, err)
		}

		var spec struct {
			ID       string   `yaml:"id"`
			Requires []string `yaml:"requires"`
		}

		err = yaml.Unmarshal(data, &spec)
		if err != nil {
			return fmt.Errorf("failed to parse %s: %w", path, err)
		}

		if spec.ID == "" {
			// Use directory name as ID if not specified
			spec.ID = filepath.Base(filepath.Dir(path))
		}

		dependency := SpecDependency{
			ID:       spec.ID,
			Requires: spec.Requires,
			Path:     path,
		}

		graph.Specs = append(graph.Specs, dependency)
		graph.Edges[spec.ID] = spec.Requires

		return nil
	})

	if err != nil {
		return nil, err
	}

	return graph, nil
}

func detectCycles(graph *DependencyGraph) []string {
	visited := make(map[string]bool)
	recStack := make(map[string]bool)
	cycles := []string{}

	var dfs func(node string, path []string) bool
	dfs = func(node string, path []string) bool {
		if recStack[node] {
			// Found cycle
			cyclePath := append(path, node)
			cycles = append(cycles, strings.Join(cyclePath, " -> "))
			return true
		}

		if visited[node] {
			return false
		}

		visited[node] = true
		recStack[node] = true

		for _, dep := range graph.Edges[node] {
			newPath := append(path, node)
			if dfs(dep, newPath) {
				return true
			}
		}

		recStack[node] = false
		return false
	}

	for _, spec := range graph.Specs {
		if !visited[spec.ID] {
			dfs(spec.ID, []string{})
		}
	}

	return cycles
}

func findImpactedBundles(graph DependencyGraph, changedFiles []string) []string {
	impacted := make(map[string]bool)

	// Find specs that were directly changed
	for _, file := range changedFiles {
		if strings.Contains(file, "bundles/") && strings.HasSuffix(file, "spec.yaml") {
			// Extract bundle name from path
			parts := strings.Split(file, "/")
			if len(parts) >= 2 {
				bundleName := parts[1]
				impacted[bundleName] = true
			}
		}
	}

	// Find downstream dependencies
	changed := true
	for changed {
		changed = false
		for specID, deps := range graph.Edges {
			for _, dep := range deps {
				if impacted[dep] && !impacted[specID] {
					impacted[specID] = true
					changed = true
				}
			}
		}
	}

	// Convert to sorted slice
	result := []string{}
	for bundle := range impacted {
		result = append(result, bundle)
	}
	sort.Strings(result)

	return result
}
