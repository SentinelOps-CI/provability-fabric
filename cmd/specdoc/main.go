// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"

	"gopkg.in/yaml.v3"
)

type SpecDoc struct {
	Meta               map[string]interface{} `yaml:"meta"`
	Requirements       map[string]Requirement `yaml:"requirements"`
	NonFunctional      map[string]Requirement `yaml:"nonFunctional"`
	AcceptanceCriteria map[string]Criterion   `yaml:"acceptanceCriteria"`
	Trace              map[string][]string    `yaml:"trace"`
}

type Requirement struct {
	Statement string `yaml:"statement"`
	Rationale string `yaml:"rationale"`
	Metric    string `yaml:"metric"`
	Owner     string `yaml:"owner"`
	Priority  string `yaml:"priority"`
}

type Criterion struct {
	Description string `yaml:"description"`
	TestVector  string `yaml:"testVector"`
}

type DocData struct {
	ID                 string
	Requirements       []RequirementItem
	NonFunctional      []RequirementItem
	AcceptanceCriteria []CriterionItem
	Traceability       string
	LedgerQuery        string
	GeneratedAt        string
}

type RequirementItem struct {
	ID        string
	Statement string
	Rationale string
	Metric    string
	Owner     string
	Priority  string
}

type CriterionItem struct {
	ID          string
	Description string
	TestVector  string
}

func main() {
	if len(os.Args) < 3 {
		fmt.Println("Usage: specdoc generate <spec.yaml> --out <output.md>")
		os.Exit(1)
	}

	if os.Args[1] != "generate" {
		fmt.Println("Unknown command. Use 'generate'")
		os.Exit(1)
	}

	specFile := os.Args[2]
	outputFile := "docs/generated/spec.md"

	// Parse command line flags
	for i, arg := range os.Args {
		if arg == "--out" && i+1 < len(os.Args) {
			outputFile = os.Args[i+1]
		}
	}

	// Read and parse spec file
	data, err := os.ReadFile(specFile)
	if err != nil {
		fmt.Printf("Error reading spec file: %v\n", err)
		os.Exit(1)
	}

	var spec SpecDoc
	if err := yaml.Unmarshal(data, &spec); err != nil {
		fmt.Printf("Error parsing YAML: %v\n", err)
		os.Exit(1)
	}

	// Generate documentation
	if err := generateDocs(spec, outputFile); err != nil {
		fmt.Printf("Error generating docs: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("✅ Documentation generated: %s\n", outputFile)
}

func generateDocs(spec SpecDoc, outputFile string) error {
	// Extract ID from spec file path
	id := extractID(outputFile)
	if id == "" {
		id = "unknown"
	}

	// Prepare requirements
	var requirements []RequirementItem
	for id, req := range spec.Requirements {
		requirements = append(requirements, RequirementItem{
			ID:        id,
			Statement: req.Statement,
			Rationale: req.Rationale,
			Metric:    req.Metric,
			Owner:     req.Owner,
			Priority:  req.Priority,
		})
	}

	// Prepare non-functional requirements
	var nonFunctional []RequirementItem
	for id, req := range spec.NonFunctional {
		nonFunctional = append(nonFunctional, RequirementItem{
			ID:        id,
			Statement: req.Statement,
			Rationale: req.Rationale,
			Metric:    req.Metric,
			Owner:     req.Owner,
			Priority:  req.Priority,
		})
	}

	// Prepare acceptance criteria
	var acceptanceCriteria []CriterionItem
	for id, criterion := range spec.AcceptanceCriteria {
		acceptanceCriteria = append(acceptanceCriteria, CriterionItem{
			ID:          id,
			Description: criterion.Description,
			TestVector:  criterion.TestVector,
		})
	}

	// Generate traceability matrix
	traceability := generateTraceabilityMatrix(spec.Trace, requirements, nonFunctional, acceptanceCriteria)

	// Generate ledger query
	ledgerQuery := generateLedgerQuery(id)

	// Prepare template data
	data := DocData{
		ID:                 id,
		Requirements:       requirements,
		NonFunctional:      nonFunctional,
		AcceptanceCriteria: acceptanceCriteria,
		Traceability:       traceability,
		LedgerQuery:        ledgerQuery,
		GeneratedAt:        "2025-01-27",
	}

	// Create output directory
	outputDir := filepath.Dir(outputFile)
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	// Generate markdown using string concatenation instead of template
	markdown := generateMarkdown(data)

	file, err := os.Create(outputFile)
	if err != nil {
		return fmt.Errorf("failed to create output file: %w", err)
	}
	defer file.Close()

	if _, err := file.WriteString(markdown); err != nil {
		return fmt.Errorf("failed to write output file: %w", err)
	}

	return nil
}

func generateMarkdown(data DocData) string {
	var lines []string

	lines = append(lines, "# Specification Documentation: "+data.ID)
	lines = append(lines, "")
	lines = append(lines, "## Requirements")
	lines = append(lines, "")
	lines = append(lines, "| ID | Statement | Rationale | Metric | Owner | Priority |")
	lines = append(lines, "|----|-----------|-----------|--------|-------|----------|")

	for _, req := range data.Requirements {
		lines = append(lines, fmt.Sprintf("| %s | %s | %s | %s | %s | %s |",
			req.ID, req.Statement, req.Rationale, req.Metric, req.Owner, req.Priority))
	}

	lines = append(lines, "")
	lines = append(lines, "## Non-Functional Requirements")
	lines = append(lines, "")
	lines = append(lines, "| ID | Statement | Rationale | Metric | Owner | Priority |")
	lines = append(lines, "|----|-----------|-----------|--------|-------|----------|")

	for _, req := range data.NonFunctional {
		lines = append(lines, fmt.Sprintf("| %s | %s | %s | %s | %s | %s |",
			req.ID, req.Statement, req.Rationale, req.Metric, req.Owner, req.Priority))
	}

	lines = append(lines, "")
	lines = append(lines, "## Acceptance Criteria")
	lines = append(lines, "")
	lines = append(lines, "| ID | Description | Test Vector |")
	lines = append(lines, "|----|-------------|-------------|")

	for _, ac := range data.AcceptanceCriteria {
		lines = append(lines, fmt.Sprintf("| %s | %s | %s |",
			ac.ID, ac.Description, ac.TestVector))
	}

	lines = append(lines, "")
	lines = append(lines, "## Traceability Matrix")
	lines = append(lines, "")
	lines = append(lines, data.Traceability)

	lines = append(lines, "")
	lines = append(lines, "## Ledger Risk History")
	lines = append(lines, "")
	lines = append(lines, "To query the risk history for this specification in the ledger:")
	lines = append(lines, "")
	lines = append(lines, "```graphql")
	lines = append(lines, data.LedgerQuery)
	lines = append(lines, "```")

	lines = append(lines, "")
	lines = append(lines, "## Generated on "+data.GeneratedAt)

	return strings.Join(lines, "\n")
}

func extractID(outputFile string) string {
	// Extract ID from path like "docs/generated/REQ-0001.md"
	re := regexp.MustCompile(`([A-Z]+-\d+)`)
	matches := re.FindStringSubmatch(outputFile)
	if len(matches) > 1 {
		return matches[1]
	}
	return ""
}

func generateTraceabilityMatrix(trace map[string][]string, requirements, nonFunctional []RequirementItem, acceptanceCriteria []CriterionItem) string {
	var lines []string
	lines = append(lines, "```mermaid")
	lines = append(lines, "graph TD")

	// Add nodes for requirements
	for _, req := range requirements {
		lines = append(lines, fmt.Sprintf("    %s[%s]", req.ID, req.ID))
	}
	for _, nfr := range nonFunctional {
		lines = append(lines, fmt.Sprintf("    %s[%s]", nfr.ID, nfr.ID))
	}

	// Add nodes for acceptance criteria
	for _, ac := range acceptanceCriteria {
		lines = append(lines, fmt.Sprintf("    %s[%s]", ac.ID, ac.ID))
	}

	// Add traceability links
	for from, toList := range trace {
		for _, to := range toList {
			lines = append(lines, fmt.Sprintf("    %s --> %s", from, to))
		}
	}

	lines = append(lines, "```")
	return strings.Join(lines, "\n")
}

func generateLedgerQuery(id string) string {
	return fmt.Sprintf(`query CapsuleRiskHistory($hash: ID!) {
  capsule(hash: $hash) {
    hash
    specSig
    riskScore
    reason
    createdAt
  }
}

# Variables:
# {
#   "hash": "%s"
# }`, id)
}
