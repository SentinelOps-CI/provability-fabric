// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"fmt"
	"os"
	"path/filepath"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func resolvePCSOpts(bundlePath string) (pcs.ValidateOptions, error) {
	wd, err := os.Getwd()
	if err != nil {
		return pcs.ValidateOptions{}, err
	}
	repoRoot, err := pcs.FindRepoRoot(wd)
	if err != nil {
		if abs, aerr := filepath.Abs(bundlePath); aerr == nil {
			repoRoot, err = pcs.FindRepoRoot(filepath.Dir(abs))
		}
	}
	if err != nil {
		return pcs.ValidateOptions{}, fmt.Errorf("%w (run from provability-fabric repo root)", err)
	}
	return pcs.ValidateOptions{
		RepoRoot:        repoRoot,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    pcs.ResolveSourceCommit(),
	}, nil
}

func verifyBundle(bundlePath string) (pcs.VerificationResult, error) {
	bundle, err := pcs.LoadScienceClaimBundle(bundlePath)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	opts, err := resolvePCSOpts(bundlePath)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	return pcs.VerifyScienceClaimBundle(bundlePath, bundle, opts)
}
