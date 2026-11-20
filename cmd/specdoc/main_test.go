package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestGeneratedMarkdownIsStableAndBounded(t *testing.T) {
	spec := SpecDoc{
		Requirements: map[string]Requirement{
			"REQ-002": {
				Statement: strings.Repeat("Long description with explicit evidence. ", 7),
				Rationale: "Second requirement rationale",
			},
			"REQ-001": {
				Statement: "First requirement",
				Owner:     "Research team",
			},
		},
		NonFunctional: map[string]Requirement{
			"NFR-002": {Statement: "Second nonfunctional"},
			"NFR-001": {Statement: "First nonfunctional"},
		},
		AcceptanceCriteria: map[string]Criterion{
			"AC-002": {Description: "Second acceptance control"},
			"AC-001": {Description: "First acceptance control"},
		},
		Trace: map[string][]string{
			"REQ-002": {"AC-002"},
			"REQ-001": {"AC-001"},
		},
	}

	var baseline string
	for i := 0; i < 20; i++ {
		file := filepath.Join(t.TempDir(), "spec.md")
		if err := generateDocs(spec, file); err != nil {
			t.Fatal(err)
		}
		raw, err := os.ReadFile(file)
		if err != nil {
			t.Fatal(err)
		}
		content := string(raw)
		if i == 0 {
			baseline = content
		} else if content != baseline {
			t.Fatal("documentation depends on unordered map iteration")
		}
		if !strings.HasSuffix(content, "\n") || strings.HasSuffix(content, "\n\n") {
			t.Fatal("generated document needs exactly one final newline")
		}
		if strings.Index(content, "### REQ-001") > strings.Index(content, "### REQ-002") ||
			strings.Index(content, "### NFR-001") > strings.Index(content, "### NFR-002") ||
			strings.Index(content, "### AC-001") > strings.Index(content, "### AC-002") {
			t.Fatal("generated documents are not ordered by stable identifiers")
		}
		for lineNumber, line := range strings.Split(strings.TrimSuffix(content, "\n"), "\n") {
			if len(line) > 80 {
				t.Fatalf("generated line %d is longer than 80 bytes: %q", lineNumber+1, line)
			}
		}
	}
}

func TestWrappedFieldDoesNotDiscardText(t *testing.T) {
	source := strings.Repeat("A carefully constructed field value. ", 12)
	formatted := strings.Join(wrappedField("Rationale", source), "\n")
	if !strings.Contains(formatted, "carefully constructed field value") {
		t.Fatalf("source content missing from generated field: %s", formatted)
	}
	for _, line := range strings.Split(formatted, "\n") {
		if len(line) > 80 {
			t.Fatalf("unbounded line %q", line)
		}
	}
}
