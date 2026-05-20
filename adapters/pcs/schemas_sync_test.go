// SPDX-License-Identifier: Apache-2.0

package pcs_test

import (
	"crypto/sha256"
	"encoding/hex"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestEmbeddedSchemasMatchConfig(t *testing.T) {
	root := repoRoot(t)
	configDir := filepath.Join(root, "config", "schemas", "pcs")
	names, err := pcs.ListEmbeddedSchemaNamesForTest()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range names {
		configPath := filepath.Join(configDir, name)
		configBytes, err := os.ReadFile(configPath)
		if err != nil {
			t.Fatalf("config schema missing %s: %v", name, err)
		}
		embedded, ok := pcs.ReadEmbeddedSchemaForTest(name)
		if !ok {
			t.Fatalf("embedded schema missing %s", name)
		}
		if hash(configBytes) != hash([]byte(embedded)) {
			t.Fatalf("schema drift: %s (sync adapters/pcs/schemas from config/schemas/pcs)", name)
		}
	}
}

func TestSchemaMirrorMatchesPCSCore(t *testing.T) {
	root := repoRoot(t)
	pcsCore := pcsCoreRoot(t)
	canonical := filepath.Join(pcsCore, "schemas")
	if st, err := os.Stat(canonical); err != nil || !st.IsDir() {
		t.Skipf("pcs-core schemas not found at %s (set PCS_CORE_PATH)", canonical)
	}
	vendor := filepath.Join(root, "config", "schemas", "pcs")
	entries, err := os.ReadDir(canonical)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range entries {
		if e.IsDir() || filepath.Ext(e.Name()) != ".json" {
			continue
		}
		want, err := os.ReadFile(filepath.Join(canonical, e.Name()))
		if err != nil {
			t.Fatal(err)
		}
		got, err := os.ReadFile(filepath.Join(vendor, e.Name()))
		if err != nil {
			t.Fatalf("provability-fabric missing schema %s: %v", e.Name(), err)
		}
		if hash(want) != hash(got) {
			t.Fatalf("schema drift vs pcs-core: %s (run: just pcs-schema-diff)", e.Name())
		}
	}
}

func TestPFExtensionSchemasMirrored(t *testing.T) {
	root := repoRoot(t)
	for _, name := range []string{
		"AdmissionBenchmarkCase.v0.schema.json",
		"PCSBenchIngest.v0.schema.json",
	} {
		configPath := filepath.Join(root, "config", "schemas", "pcs", name)
		embedded, ok := pcs.ReadEmbeddedSchemaForTest(name)
		if !ok {
			t.Fatalf("embedded schema missing %s", name)
		}
		configBytes, err := os.ReadFile(configPath)
		if err != nil {
			t.Fatalf("config schema missing %s: %v", name, err)
		}
		if hash(configBytes) != hash([]byte(embedded)) {
			t.Fatalf("PF extension schema drift: %s", name)
		}
	}
}

func hash(b []byte) string {
	sum := sha256.Sum256(b)
	return hex.EncodeToString(sum[:])
}
