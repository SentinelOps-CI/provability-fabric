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

func hash(b []byte) string {
	sum := sha256.Sum256(b)
	return hex.EncodeToString(sum[:])
}
