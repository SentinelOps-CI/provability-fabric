// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"os"
	"path/filepath"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

// Exit codes for PCS commands (sysexits-inspired).
const (
	ExitOK                 = 0
	ExitVerificationFailed = 1
	ExitError              = 2
)

func resolvePCSOpts(bundlePath string, localDev bool) (pcs.ValidateOptions, error) {
	repoRoot := ""
	if wd, err := os.Getwd(); err == nil {
		repoRoot, _ = pcs.FindRepoRoot(wd)
	}
	if repoRoot == "" {
		if abs, err := filepath.Abs(bundlePath); err == nil {
			repoRoot, _ = pcs.FindRepoRoot(filepath.Dir(abs))
		}
	}
	return pcs.ValidateOptions{
		RepoRoot:        repoRoot,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    pcs.ResolveSourceCommit(),
		LocalDev:        localDev,
	}, nil
}

func verifyBundle(bundlePath string, localDev bool) (pcs.VerificationResult, error) {
	resolved, err := pcs.ResolveArtifactPath(bundlePath)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	bundle, err := pcs.LoadScienceClaimBundle(resolved)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	opts, err := resolvePCSOpts(resolved, localDev)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	return pcs.VerifyScienceClaimBundle(resolved, bundle, opts)
}

func printVerificationFailures(result pcs.VerificationResult) {
	for _, c := range pcs.FailedChecks(result) {
		code, _ := c.Details["reason_code"].(string)
		if code != "" {
			printVerifFailure(c.CheckID, code, c.Description)
		} else {
			printVerifFailure(c.CheckID, "", c.Description)
		}
	}
}

func printVerifFailure(checkID, reasonCode, description string) {
	if reasonCode != "" {
		os.Stderr.WriteString(checkID + ": " + reasonCode + " — " + description + "\n")
		return
	}
	os.Stderr.WriteString(checkID + ": " + description + "\n")
}
