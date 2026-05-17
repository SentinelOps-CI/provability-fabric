// SPDX-License-Identifier: Apache-2.0

package pcs_test

import (
	"errors"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestMigrateLegacyBundleConvertsSingularFields(t *testing.T) {
	legacyPath := filepath.Join(repoRoot(t), "tests", "pcs", "invalid_legacy_singular_runtime_receipt.json")
	raw, err := os.ReadFile(legacyPath)
	if err != nil {
		t.Fatal(err)
	}
	out, err := pcs.MigrateLegacyBundle(raw)
	if err != nil {
		t.Fatal(err)
	}
	keys, err := pcs.DetectLegacyBundleKeys(out)
	if err != nil {
		t.Fatal(err)
	}
	if len(keys) > 0 {
		t.Fatalf("expected no legacy keys after migration, got %v", keys)
	}
	bundle, err := pcs.LoadScienceClaimBundleFromBytes(out)
	if err != nil {
		t.Fatal(err)
	}
	if bundle.PrimaryRuntimeReceipt() == nil {
		t.Fatal("expected runtime_receipts after migration")
	}
	if len(bundle.Certificates) == 0 {
		t.Fatal("expected certificates after migration")
	}
	if bundle.SchemaVersion != pcs.SchemaVersionV0 {
		t.Fatalf("schema_version want v0, got %s", bundle.SchemaVersion)
	}
}

func TestLoadRejectsLegacyWithoutMigration(t *testing.T) {
	legacyPath := filepath.Join(repoRoot(t), "tests", "pcs", "invalid_legacy_singular_runtime_receipt.json")
	_, err := pcs.LoadScienceClaimBundle(legacyPath)
	if err == nil {
		t.Fatal("expected load error for legacy bundle")
	}
	var legacy *pcs.LegacyBundleError
	if !errors.As(err, &legacy) {
		t.Fatalf("expected LegacyBundleError, got %v", err)
	}
}
