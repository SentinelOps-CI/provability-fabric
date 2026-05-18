// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"encoding/json"
	"fmt"
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

func resolvePCSOpts(bundlePath string, localDev, releaseMode bool) (pcs.ValidateOptions, error) {
	repoRoot := ""
	if wd, err := os.Getwd(); err == nil {
		repoRoot, _ = pcs.FindRepoRoot(wd)
	}
	if repoRoot == "" {
		if abs, err := filepath.Abs(bundlePath); err == nil {
			repoRoot, _ = pcs.FindRepoRoot(filepath.Dir(abs))
		}
	}
	if releaseMode && localDev {
		return pcs.ValidateOptions{}, fmt.Errorf("release-mode cannot be combined with local-dev")
	}
	if !releaseMode {
		releaseMode = pcs.ReleaseModeFromEnv()
	}
	sourceCommit, err := pcs.ResolveSourceCommitForMode(releaseMode, localDev)
	if err != nil {
		return pcs.ValidateOptions{}, err
	}
	return pcs.ValidateOptions{
		RepoRoot:        repoRoot,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    sourceCommit,
		LocalDev:        localDev,
		ReleaseMode:     releaseMode,
	}, nil
}

func verifyBundle(bundlePath string, localDev, releaseMode bool, adm resolvedScienceClaimAdmission) (pcs.VerificationResult, error) {
	resolved, err := pcs.ResolveArtifactPath(bundlePath)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	if adm.Profile != nil && adm.Profile.IsToolUseProfile() {
		opts, err := resolvePCSOpts(resolved, localDev, releaseMode)
		if err != nil {
			return pcs.VerificationResult{}, err
		}
		applyAdmissionToValidateOpts(&opts, adm)
		if err := pcs.EnforceScienceClaimAdmission(adm.Policy, adm.Handoff, adm.Registry, adm.Profile); err != nil {
			return pcs.VerificationResult{}, wrapAdmissionError(err)
		}
		if err := pcs.EnforceAdmissionProfile(adm.Profile, resolved, nil, adm.Handoff); err != nil {
			return pcs.VerificationResult{}, wrapAdmissionError(err)
		}
		return pcs.VerificationResult{}, fmt.Errorf("%s: full tool-use bundle verification is not implemented yet", pcs.FailureCodeToolUseReleaseNotImplemented)
	}
	bundle, err := pcs.LoadScienceClaimBundle(resolved)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	opts, err := resolvePCSOpts(resolved, localDev, releaseMode)
	if err != nil {
		return pcs.VerificationResult{}, err
	}
	applyAdmissionToValidateOpts(&opts, adm)
	result, err := pcs.VerifyScienceClaimBundle(resolved, bundle, opts)
	if err != nil {
		return result, wrapAdmissionError(err)
	}
	if err := pcs.ValidatePFProvenanceCommit(result.SourceCommit, opts.ReleaseMode, opts.LocalDev); err != nil {
		return result, err
	}
	return result, nil
}

func writeReleaseChainResult(bundlePath string, result pcs.VerificationResult, adm resolvedScienceClaimAdmission, outPath string, localDev, releaseMode bool) error {
	opts, err := resolveReleaseChainOpts(localDev, releaseMode)
	if err != nil {
		return err
	}
	opts.AllowSkippedRegistrySemantics = adm.Policy.AllowSkippedRegistrySemantics
	opts.Registry = adm.Registry
	opts.AdmissionProfile = adm.Profile
	if adm.Manifest != nil {
		if resolved, err := pcs.ResolveArtifactPath(bundlePath); err == nil {
			opts.ArtifactDir = filepath.Dir(resolved)
		}
	}
	var handoff *pcs.HandoffManifest
	if adm.Handoff != nil && adm.Handoff.Manifest != nil {
		handoff = adm.Handoff.Manifest
	}
	manifest := adm.Manifest
	manifestPath := ""
	if manifest == nil {
		manifest = &pcs.ReleaseManifest{
			ReleaseID:        "release-pf-science-claim",
			ReleaseCandidate: "pf-verify",
		}
	} else if adm.Manifest != nil {
		if def, ok := pcs.DefaultReleaseManifestPath(opts.ArtifactDir); ok {
			manifestPath = def
		}
	}
	rcvr, err := pcs.BuildReleaseChainValidationResultFromVerification(manifest, manifestPath, result, handoff, adm.Registry, opts)
	if err != nil {
		return err
	}
	data, err := json.MarshalIndent(rcvr, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(outPath, data, 0644); err != nil {
		return fmt.Errorf("write release chain validation result: %w", err)
	}
	return nil
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
