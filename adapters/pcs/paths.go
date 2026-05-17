// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// ResolveArtifactPath returns an absolute path to a bundle or signed-bundle JSON file.
// It accepts paths relative to the current working directory or to the provability-fabric repo root,
// so pf can be run from core/cli/pf without broken ../../ segments.
func ResolveArtifactPath(userPath string) (string, error) {
	userPath = strings.TrimSpace(userPath)
	if userPath == "" {
		return "", fmt.Errorf("empty path")
	}

	try := func(p string) (string, bool) {
		p = filepath.Clean(p)
		st, err := os.Stat(p)
		if err != nil || st.IsDir() {
			return "", false
		}
		abs, err := filepath.Abs(p)
		if err != nil {
			return p, true
		}
		return abs, true
	}

	wd, wdErr := os.Getwd()
	// Prefer repo-root tests/pcs over shadow copies (e.g. core/cli/pf/tests/pcs from an earlier sign).
	if wdErr == nil {
		if tail := pathTailFromTestsPCS(userPath); tail != "" {
			if root, err := FindRepoRoot(wd); err == nil {
				if p, ok := try(filepath.Join(root, tail)); ok {
					return p, nil
				}
			}
		}
	}

	if p, ok := try(userPath); ok {
		return p, nil
	}
	if abs, err := filepath.Abs(userPath); err == nil {
		if p, ok := try(abs); ok {
			return p, nil
		}
	}

	if wdErr != nil {
		return "", fmt.Errorf("artifact not found: %s", userPath)
	}

	var candidates []string
	if root, err := FindRepoRoot(wd); err == nil {
		candidates = append(candidates,
			filepath.Join(root, userPath),
			filepath.Join(root, filepath.Base(userPath)),
			filepath.Join(root, "tests", "pcs", filepath.Base(userPath)),
		)
		if tail := pathTailFromTestsPCS(userPath); tail != "" {
			candidates = append(candidates, filepath.Join(root, tail))
		}
	}

	// If cwd is inside the repo (e.g. core/cli/pf), try resolving from each ancestor.
	for dir := wd; ; {
		candidates = append(candidates,
			filepath.Join(dir, userPath),
			filepath.Join(dir, filepath.Base(userPath)),
		)
		if tail := pathTailFromTestsPCS(userPath); tail != "" {
			candidates = append(candidates, filepath.Join(dir, tail))
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}

	seen := make(map[string]struct{})
	for _, c := range candidates {
		c = filepath.Clean(c)
		if _, dup := seen[c]; dup {
			continue
		}
		seen[c] = struct{}{}
		if p, ok := try(c); ok {
			return p, nil
		}
	}

	return "", fmt.Errorf("artifact not found: %s (cwd: %s; hint: use tests/pcs/<file>.json from repo root or an absolute path)", userPath, wd)
}

// pathTailFromTestsPCS extracts tests/pcs/<file> from inputs like ../../tests/pcs/foo.json.
func pathTailFromTestsPCS(userPath string) string {
	slash := filepath.ToSlash(userPath)
	const marker = "tests/pcs/"
	if idx := strings.Index(slash, marker); idx >= 0 {
		return filepath.FromSlash(slash[idx:])
	}
	return ""
}

// ResolveOutputPath resolves an output file path (repo-relative when appropriate).
func ResolveOutputPath(userPath string) (string, error) {
	userPath = strings.TrimSpace(userPath)
	if userPath == "" {
		return "", fmt.Errorf("empty output path")
	}
	if filepath.IsAbs(userPath) {
		return filepath.Clean(userPath), nil
	}
	wd, err := os.Getwd()
	if err != nil {
		return filepath.Clean(userPath), nil
	}

	var candidates []string
	// Prefer repo-root tests/pcs paths so sign from core/cli/pf does not write under core/cli/pf/tests/.
	if tail := pathTailFromTestsPCS(userPath); tail != "" {
		if root, err := FindRepoRoot(wd); err == nil {
			candidates = append(candidates, filepath.Join(root, tail))
		}
	}
	if root, err := FindRepoRoot(wd); err == nil {
		candidates = append(candidates,
			filepath.Join(root, userPath),
			filepath.Join(root, filepath.Base(userPath)),
		)
	}
	candidates = append(candidates, filepath.Join(wd, userPath))

	seen := make(map[string]struct{})
	for _, c := range candidates {
		c = filepath.Clean(c)
		if _, dup := seen[c]; dup {
			continue
		}
		seen[c] = struct{}{}
		dir := filepath.Dir(c)
		if st, err := os.Stat(dir); err == nil && st.IsDir() {
			return c, nil
		}
		if err := os.MkdirAll(dir, 0755); err == nil {
			return c, nil
		}
	}
	return filepath.Clean(filepath.Join(wd, userPath)), nil
}
