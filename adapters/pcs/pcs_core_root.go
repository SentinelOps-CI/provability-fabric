// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// ResolvePCSCoreRoot locates a pcs-core checkout (PCS_CORE_PATH, repo/pcs-core, or ../pcs-core).
func ResolvePCSCoreRoot(from string) (string, error) {
	if p := strings.TrimSpace(os.Getenv("PCS_CORE_PATH")); p != "" {
		if abs, err := filepath.Abs(p); err == nil {
			if hasPCSCoreSchemas(abs) {
				return abs, nil
			}
		}
	}
	root := strings.TrimSpace(from)
	if root == "" {
		if wd, err := os.Getwd(); err == nil {
			root = wd
		}
	}
	if repo, err := FindRepoRoot(root); err == nil {
		root = repo
	}
	for _, candidate := range []string{
		filepath.Join(root, "pcs-core"),
		filepath.Join(root, "..", "pcs-core"),
	} {
		if abs, err := filepath.Abs(candidate); err == nil && hasPCSCoreSchemas(abs) {
			return abs, nil
		}
	}
	return "", fmt.Errorf("pcs-core not found (set PCS_CORE_PATH or clone adjacent to provability-fabric)")
}

func hasPCSCoreSchemas(root string) bool {
	st, err := os.Stat(filepath.Join(root, "schemas", "BenchmarkReport.v0.schema.json"))
	return err == nil && !st.IsDir()
}
