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

type validateResult struct {
	File   string `json:"file"`
	Status string `json:"status"`
	Error  string `json:"error,omitempty"`
}

func main() {
	fixturesDir := flag.String("fixtures", "tests/pcs", "Directory containing PCS JSON fixtures")
	repoRoot := flag.String("repo-root", "", "Provability-fabric repo root (auto-detected if empty)")
	localDev := flag.Bool("local-dev", false, "Allow 40-zero source_commit placeholder")
	labtrust := flag.Bool("labtrust", true, "Also validate tests/pcs/fixtures/labtrust canonical fixtures")
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

	var results []validateResult
	failed := validateBundleFixtures(dir, root, *localDev, &results)

	if *labtrust {
		labtrustDir := filepath.Join(dir, "fixtures", "labtrust")
		failed += validateLabtrustFixtures(labtrustDir, root, *localDev, &results)
		releaseDir := filepath.Join(dir, "fixtures", "labtrust-release")
		failed += validateLabtrustReleaseFixtures(releaseDir, root, *localDev, &results)
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
		fmt.Printf("OK: PCS fixture validation passed (%d artifacts)\n", len(results))
	}
}

func validateBundleFixtures(dir, root string, localDev bool, results *[]validateResult) int {
	entries, err := os.ReadDir(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read fixtures: %v\n", err)
		os.Exit(2)
	}

	var failed int
	for _, e := range entries {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".json") {
			continue
		}
		if shouldSkipFixtureName(e.Name()) {
			continue
		}
		path := filepath.Join(dir, e.Name())
		expectFail := strings.HasPrefix(e.Name(), "invalid_")
		if validateScienceClaimBundle(path, e.Name(), root, localDev, expectFail, results) {
			failed++
		}
	}
	return failed
}

func validateLabtrustReleaseFixtures(releaseDir, root string, localDev bool, results *[]validateResult) int {
	if _, err := os.Stat(releaseDir); err != nil {
		return 0
	}
	var failed int
	certified := filepath.Join(releaseDir, "science_claim_bundle.certified.json")
	if _, err := os.Stat(certified); err == nil {
		label := "fixtures/labtrust-release/science_claim_bundle.certified.json"
		if validateScienceClaimBundle(certified, label, root, localDev, false, results) {
			failed++
		}
	}
	vrPath := filepath.Join(releaseDir, "verification_result.json")
	if _, err := os.Stat(vrPath); err == nil {
		label := "fixtures/labtrust-release/verification_result.json"
		if validateVerificationResultFile(vrPath, label, root, results) {
			failed++
		}
	}
	signed := filepath.Join(releaseDir, "signed_science_claim_bundle.json")
	if _, err := os.Stat(signed); err == nil {
		label := "fixtures/labtrust-release/signed_science_claim_bundle.json"
		if validateSignedBundle(signed, label, root, results) {
			failed++
		}
	}
	for _, spec := range []struct {
		file   string
		schema string
	}{
		{"handoff_to_pf.json", "handoff"},
		{"release_manifest.json", "release_manifest"},
		{"artifact_registry.json", "artifact_registry"},
		{"release_chain_validation_result.json", "release_chain_result"},
	} {
		path := filepath.Join(releaseDir, spec.file)
		if _, err := os.Stat(path); err != nil {
			continue
		}
		label := filepath.ToSlash(filepath.Join("fixtures", "labtrust-release", spec.file))
		if validatePhase2ProtocolFixture(path, label, root, spec.schema, results) {
			failed++
		}
	}
	entries, _ := os.ReadDir(releaseDir)
	for _, e := range entries {
		if e.IsDir() || !strings.HasPrefix(e.Name(), "invalid_") {
			continue
		}
		path := filepath.Join(releaseDir, e.Name())
		label := filepath.ToSlash(filepath.Join("fixtures", "labtrust-release", e.Name()))
		if validateScienceClaimBundle(path, label, root, localDev, true, results) {
			failed++
		}
	}
	return failed
}

func validatePhase2ProtocolFixture(path, label, root, kind string, results *[]validateResult) bool {
	switch kind {
	case "handoff":
		if err := pcs.ValidateHandoffManifestFile(root, path); err != nil {
			*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
			return true
		}
	case "release_manifest":
		if err := pcs.ValidateReleaseManifestFile(root, path); err != nil {
			*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
			return true
		}
	case "artifact_registry":
		if err := pcs.ValidateArtifactRegistryFile(root, path); err != nil {
			*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
			return true
		}
	case "release_chain_result":
		data, err := os.ReadFile(path)
		if err != nil {
			*results = append(*results, validateResult{File: label, Status: "load_error", Error: err.Error()})
			return true
		}
		var result pcs.ReleaseChainValidationResult
		if err := json.Unmarshal(data, &result); err != nil {
			*results = append(*results, validateResult{File: label, Status: "parse_error", Error: err.Error()})
			return true
		}
		if err := pcs.ValidateReleaseChainValidationResult(root, result); err != nil {
			*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
			return true
		}
	default:
		*results = append(*results, validateResult{File: label, Status: "internal_error", Error: "unknown phase2 fixture kind"})
		return true
	}
	*results = append(*results, validateResult{File: label, Status: "schema_valid"})
	return false
}

func validateVerificationResultFile(path, label, root string, results *[]validateResult) bool {
	data, err := os.ReadFile(path)
	if err != nil {
		*results = append(*results, validateResult{File: label, Status: "load_error", Error: err.Error()})
		return true
	}
	var result pcs.VerificationResult
	if err := json.Unmarshal(data, &result); err != nil {
		*results = append(*results, validateResult{File: label, Status: "parse_error", Error: err.Error()})
		return true
	}
	if err := pcs.ValidateVerificationResult(root, result); err != nil {
		*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
		return true
	}
	if !pcs.VerificationPassed(result) {
		*results = append(*results, validateResult{File: label, Status: "unexpected_status", Error: result.Status})
		return true
	}
	*results = append(*results, validateResult{File: label, Status: result.Status})
	return false
}

func validateLabtrustFixtures(labtrustDir, root string, localDev bool, results *[]validateResult) int {
	var failed int
	certified := filepath.Join(labtrustDir, "science_claim_bundle.certified.json")
	if _, err := os.Stat(certified); err == nil {
		label := "fixtures/labtrust/science_claim_bundle.certified.json"
		if validateScienceClaimBundle(certified, label, root, localDev, false, results) {
			failed++
		}
	}
	signed := filepath.Join(labtrustDir, "signed_science_claim_bundle.json")
	if _, err := os.Stat(signed); err == nil {
		label := "fixtures/labtrust/signed_science_claim_bundle.json"
		if validateSignedBundle(signed, label, root, results) {
			failed++
		}
	}
	export := filepath.Join(labtrustDir, "signed_science_claim_bundle.labtrust-export.json")
	if _, err := os.Stat(export); err == nil {
		label := "fixtures/labtrust/signed_science_claim_bundle.labtrust-export.json"
		if validateSignedBundleExport(export, label, root, results) {
			failed++
		}
	}
	return failed
}

func validateScienceClaimBundle(path, label, root string, localDev, expectFail bool, results *[]validateResult) bool {
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		if expectFail {
			*results = append(*results, validateResult{File: label, Status: "LoadRejected"})
			return false
		}
		*results = append(*results, validateResult{File: label, Status: "load_error", Error: err.Error()})
		return true
	}
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "pcs-validate",
		LocalDev:        localDev,
	}
	vr, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		*results = append(*results, validateResult{File: label, Status: "error", Error: err.Error()})
		return true
	}
	if expectFail && pcs.VerificationPassed(vr) {
		*results = append(*results, validateResult{File: label, Status: "unexpected_pass"})
		return true
	}
	if !expectFail && !pcs.VerificationPassed(vr) {
		*results = append(*results, validateResult{File: label, Status: "unexpected_fail"})
		return true
	}
	*results = append(*results, validateResult{File: label, Status: vr.Status})
	return false
}

func validateSignedBundle(path, label, root string, results *[]validateResult) bool {
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		*results = append(*results, validateResult{File: label, Status: "load_error", Error: err.Error()})
		return true
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
		return true
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
		*results = append(*results, validateResult{File: label, Status: "integrity_failed", Error: err.Error()})
		return true
	}
	if !pcs.VerificationPassed(signed.VerificationResult) {
		*results = append(*results, validateResult{File: label, Status: "unexpected_embedded_status", Error: signed.VerificationResult.Status})
		return true
	}
	*results = append(*results, validateResult{File: label, Status: "ProofChecked"})
	return false
}

func validateSignedBundleExport(path, label, root string, results *[]validateResult) bool {
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		*results = append(*results, validateResult{File: label, Status: "load_error", Error: err.Error()})
		return true
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		*results = append(*results, validateResult{File: label, Status: "schema_invalid", Error: err.Error()})
		return true
	}
	*results = append(*results, validateResult{File: label, Status: "schema_valid"})
	return false
}

func shouldSkipFixtureName(name string) bool {
	if strings.Contains(name, "snapshot") || strings.Contains(name, "trace_certificate") {
		return true
	}
	return name == "signed_science_claim_bundle.demo.json"
}
