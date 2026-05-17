// SPDX-License-Identifier: Apache-2.0
// Command pcs-validate runs PCS fixture and schema validation (CI and local release gates).

package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func main() {
	fixturesDir := flag.String("fixtures", "tests/pcs", "Directory containing PCS JSON fixtures")
	repoRoot := flag.String("repo-root", "", "Provability-fabric repo root (auto-detected if empty)")
	localDev := flag.Bool("local-dev", false, "Allow 40-zero source_commit placeholder")
	jsonOut := flag.Bool("json", false, "Emit machine-readable summary")
	flag.Parse()

	root := *repoRoot
	if root == "" {
		wd, _ := os.Getwd()
		var err error
		root, err = pcs.FindRepoRoot(wd)
		if err != nil {
			fmt.Fprintf(os.Stderr, "repo root: %v\n", err)
			os.Exit(2)
		}
	}

	wd, _ := os.Getwd()
	dir := *fixturesDir
	if !filepath.IsAbs(dir) {
		dir = filepath.Join(wd, dir)
	}
	dir = filepath.Clean(dir)

	type result struct {
		File   string `json:"file"`
		Status string `json:"status"`
		Error  string `json:"error,omitempty"`
	}

	var results []result
	var failed int

	entries, err := os.ReadDir(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read fixtures: %v\n", err)
		os.Exit(2)
	}

	for _, e := range entries {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".json") {
			continue
		}
		if strings.Contains(e.Name(), "snapshot") || strings.Contains(e.Name(), "trace_certificate") {
			continue
		}
		if e.Name() == "signed_science_claim_bundle.demo.json" {
			continue
		}
		path := filepath.Join(dir, e.Name())
		expectFail := strings.HasPrefix(e.Name(), "invalid_")
		bundle, err := pcs.LoadScienceClaimBundle(path)
		if err != nil {
			if expectFail {
				results = append(results, result{File: e.Name(), Status: "LoadRejected"})
				continue
			}
			results = append(results, result{File: e.Name(), Status: "load_error", Error: err.Error()})
			failed++
			continue
		}
		opts := pcs.ValidateOptions{
			RepoRoot:        root,
			VerifierVersion: pcs.DefaultVerifierVersion,
			SourceCommit:    "pcs-validate",
			LocalDev:        *localDev,
		}
		vr, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
		if err != nil {
			results = append(results, result{File: e.Name(), Status: "error", Error: err.Error()})
			failed++
			continue
		}

		if expectFail && pcs.VerificationPassed(vr) {
			results = append(results, result{File: e.Name(), Status: "unexpected_pass"})
			failed++
			continue
		}
		if !expectFail && !pcs.VerificationPassed(vr) {
			results = append(results, result{File: e.Name(), Status: "unexpected_fail"})
			failed++
			continue
		}
		results = append(results, result{File: e.Name(), Status: vr.Status})
	}

	if *jsonOut {
		enc := json.NewEncoder(os.Stdout)
		enc.SetIndent("", "  ")
		_ = enc.Encode(map[string]any{"results": results, "failed": failed})
	} else {
		for _, r := range results {
			fmt.Printf("%s: %s\n", r.File, r.Status)
			if r.Error != "" {
				fmt.Printf("  %s\n", r.Error)
			}
		}
	}

	if failed > 0 {
		os.Exit(1)
	}
	if !*jsonOut {
		var negative, positive int
		for _, r := range results {
			if strings.HasPrefix(r.File, "invalid_") {
				negative++
			} else {
				positive++
			}
		}
		fmt.Printf("OK: %d negative fixtures rejected, %d positive fixture passed\n", negative, positive)
	}
}
