package main

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// A failed encryption path must never publish the temporary plaintext ZIP.
// The existing destination must also remain unchanged on error.
func TestDSARFailedEncryptionPreservesOutput(t *testing.T) {
	for _, existing := range []bool{false, true} {
		t.Run(map[bool]string{false: "new-output", true: "existing-output"}[existing], func(t *testing.T) {
			dir := t.TempDir()
			output := filepath.Join(dir, "export.zip")
			if existing {
				if err := os.WriteFile(output, []byte("existing encrypted export"), 0600); err != nil {
					t.Fatal(err)
				}
			}
			exporter := DSARExporter{
				outputPath: output,
				publicKeyPath: filepath.Join(dir, "missing-public-key.asc"),
			}
			err := exporter.createEncryptedZip(DSARData{
				TenantID: "fixture-tenant",
				Metadata: map[string]interface{}{"export_version": "1.0"},
			})
			if err == nil || !strings.Contains(err.Error(), "public key") {
				t.Fatalf("expected missing-key encryption failure, got %v", err)
			}
			bytes, err := os.ReadFile(output)
			if existing {
				if err != nil || string(bytes) != "existing encrypted export" {
					t.Fatalf("failed operation changed existing output: %v, %q", err, bytes)
				}
			} else if !errors.Is(err, os.ErrNotExist) {
				t.Fatalf("failed operation published output: %v", err)
			}
			matches, err := filepath.Glob(filepath.Join(dir, ".dsar-export-*"))
			if err != nil || len(matches) != 0 {
				t.Fatalf("failed operation left temporary archives: %v, %v", matches, err)
			}
		})
	}
}
