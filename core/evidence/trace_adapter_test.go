// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

func TestImportKITSimpleTrace(t *testing.T) {
	root := repoRoot(t)
	kitPath := filepath.Join(root, "tests", "replay", "bundles", "simple", "trace.json")
	trace, err := ImportKITTrace(kitPath, "simple-import")
	if err != nil {
		t.Fatalf("import: %v", err)
	}
	if trace.TraceID != "simple-import" {
		t.Fatalf("trace_id: %s", trace.TraceID)
	}
	if len(trace.Events) != 2 {
		t.Fatalf("expected 2 events, got %d", len(trace.Events))
	}
	if trace.Events[0].Kind != "function_call" {
		t.Fatalf("first kind: %s", trace.Events[0].Kind)
	}
	expected, err := CanonicalJSONDigest(trace, "trace_digest")
	if err != nil {
		t.Fatal(err)
	}
	if trace.TraceDigest != expected {
		t.Fatalf("digest mismatch")
	}
}

func TestImportKITTraceRoundTripValidate(t *testing.T) {
	root := repoRoot(t)
	kitPath := filepath.Join(root, "tests", "replay", "bundles", "simple", "trace.json")
	trace, err := ImportKITTrace(kitPath, "")
	if err != nil {
		t.Fatalf("import: %v", err)
	}
	out := filepath.Join(t.TempDir(), "execution-trace.json")
	if err := WriteExecutionTrace(out, trace); err != nil {
		t.Fatal(err)
	}
	body, err := os.ReadFile(out)
	if err != nil {
		t.Fatal(err)
	}
	schemaPath := filepath.Join(root, "specs", "evidence", "v0.1", "schemas", "execution-trace.schema.json")
	if err := validateAgainstSchema(schemaPath, body); err != nil {
		t.Fatalf("schema validate: %v", err)
	}
	var parsed map[string]any
	if err := json.Unmarshal(body, &parsed); err != nil {
		t.Fatal(err)
	}
	digest, err := CanonicalJSONDigest(parsed, "trace_digest")
	if err != nil {
		t.Fatal(err)
	}
	if digest != trace.TraceDigest {
		t.Fatalf("round-trip digest mismatch")
	}
}
