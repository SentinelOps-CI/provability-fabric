// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
	"github.com/spf13/cobra"
)

func releaseChainVerifyCmd() *cobra.Command {
	var manifestPath string
	var registryPath string
	var artifactDir string
	var outPath string
	var localDev bool
	var releaseMode bool
	var allowSkippedRegistrySemantics bool
	var admissionProfileID string

	cmd := &cobra.Command{
		Use:   "release-chain",
		Short: "Verify a PCS release chain from ReleaseManifest.v0",
		Long:  `Validate artifact hashes, producer commits, and ArtifactRegistry.v0 admission; emit ReleaseChainValidationResult.v0.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if strings.TrimSpace(manifestPath) == "" {
				return fmt.Errorf("--manifest ReleaseManifest.v0 is required")
			}
			opts, _, err := resolveReleaseChainAdmission(manifestPath, registryPath, artifactDir, admissionProfileID, allowSkippedRegistrySemantics, localDev, releaseMode)
			if err != nil {
				return wrapAdmissionError(err)
			}
			result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
			if err != nil {
				return wrapAdmissionError(err)
			}
			if outPath != "" {
				data, err := json.MarshalIndent(result, "", "  ")
				if err != nil {
					return err
				}
				if err := os.WriteFile(outPath, data, 0644); err != nil {
					return fmt.Errorf("write release chain validation result: %w", err)
				}
			}
			fmt.Printf("validation_id: %s\n", result.ValidationID)
			fmt.Printf("status: %s\n", result.Status)
			fmt.Printf("artifacts_checked: %d\n", result.ArtifactsChecked)
			for _, c := range result.Checks {
				fmt.Printf("  [%s] %s\n", c.Status, c.CheckID)
			}
			if outPath != "" {
				fmt.Printf("wrote %s\n", outPath)
			}
			if result.Status != pcs.StatusProofChecked {
				fmt.Println(pcs.FormatFailureExplanations(pcs.ExplainReleaseChainFailures(result)))
				return cliExit(ExitVerificationFailed, fmt.Errorf("release chain validation failed"))
			}
			return nil
		},
	}
	cmd.Flags().StringVar(&manifestPath, "manifest", "", "ReleaseManifest.v0 JSON path")
	cmd.Flags().StringVar(&registryPath, "registry", "", "ArtifactRegistry.v0 JSON path (required in release mode; defaults to PCS_CORE_PATH/examples/artifact_registry.valid.json)")
	cmd.Flags().StringVar(&artifactDir, "artifact-dir", "", "Directory containing manifest artifact files (default: manifest directory)")
	cmd.Flags().StringVar(&outPath, "out", "", "Write ReleaseChainValidationResult.v0 JSON")
	cmd.Flags().BoolVar(&localDev, "local-dev", false, "Allow placeholder source_commit (local development only)")
	cmd.Flags().BoolVar(&releaseMode, "release-mode", false, "Require registry and reject placeholder commits")
	cmd.Flags().BoolVar(&allowSkippedRegistrySemantics, "allow-skipped-registry-semantics", false, "Allow registry semantic checks PF does not execute (local development only)")
	cmd.Flags().StringVar(&admissionProfileID, "admission-profile", "", "Admission profile id (e.g. labtrust_qc_release); required in release mode")
	return cmd
}

func resolveReleaseChainOpts(localDev, releaseMode bool) (pcs.ReleaseChainVerifyOptions, error) {
	repoRoot := ""
	if wd, err := os.Getwd(); err == nil {
		repoRoot, _ = pcs.FindRepoRoot(wd)
	}
	if releaseMode && localDev {
		return pcs.ReleaseChainVerifyOptions{}, fmt.Errorf("release-mode cannot be combined with local-dev")
	}
	if !releaseMode {
		releaseMode = pcs.ReleaseModeFromEnv()
	}
	sourceCommit, err := pcs.ResolveSourceCommitForMode(releaseMode, localDev)
	if err != nil {
		return pcs.ReleaseChainVerifyOptions{}, err
	}
	return pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot,
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:     sourceCommit,
		ReleaseMode:      releaseMode,
	}, nil
}
