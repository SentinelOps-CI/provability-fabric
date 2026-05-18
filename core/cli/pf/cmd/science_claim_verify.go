// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"encoding/json"
	"fmt"
	"os"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
	"github.com/spf13/cobra"
)

func verifyRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "verify",
		Short: "Verify PCS artifacts",
		Long:  `Verify Proof-Carrying Science artifacts such as ScienceClaimBundle.v0.`,
	}
	cmd.AddCommand(scienceClaimVerifyCmd())
	cmd.AddCommand(releaseChainVerifyCmd())
	return cmd
}

func scienceClaimVerifyCmd() *cobra.Command {
	var jsonOut bool
	var outPath string
	var handoffPath string
	var registryPath string
	var manifestPath string
	var releaseChainOut string
	var localDev bool
	var releaseMode bool
	var allowMissingHandoff bool
	var allowSkippedRegistrySemantics bool
	var admissionProfileID string

	cmd := &cobra.Command{
		Use:   "science-claim <bundle.json>",
		Short: "Verify a ScienceClaimBundle.v0",
		Long:  `Run required consistency, provenance, and certificate checks on a LabTrust-certified science claim bundle.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			bundlePath := args[0]
			adm, err := resolveScienceClaimAdmission(scienceClaimAdmissionInput{
				HandoffPath:                   handoffPath,
				RegistryPath:                  registryPath,
				ManifestPath:                  manifestPath,
				AdmissionProfileID:            admissionProfileID,
				AllowMissingHandoff:           allowMissingHandoff,
				AllowSkippedRegistrySemantics: allowSkippedRegistrySemantics,
				LocalDev:                      localDev,
				ReleaseMode:                   releaseMode,
				BundlePath:                    bundlePath,
			})
			if err != nil {
				return wrapAdmissionError(err)
			}
			result, err := verifyBundle(bundlePath, localDev, releaseMode, adm)
			if err != nil {
				return err
			}

			if releaseChainOut != "" {
				if err := writeReleaseChainResult(bundlePath, result, adm, releaseChainOut, localDev, releaseMode); err != nil {
					return err
				}
			}

			if outPath != "" {
				data, err := json.MarshalIndent(result, "", "  ")
				if err != nil {
					return err
				}
				if err := os.WriteFile(outPath, data, 0644); err != nil {
					return fmt.Errorf("write verification result: %w", err)
				}
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				if err := enc.Encode(result); err != nil {
					return err
				}
			} else {
				fmt.Printf("verification_id: %s\n", result.VerificationID)
				fmt.Printf("status: %s\n", result.Status)
				fmt.Printf("bundle_id: %s\n", result.BundleID)
				fmt.Printf("checks: %d\n", len(result.Checks))
				for _, c := range result.Checks {
					fmt.Printf("  [%s] %s\n", c.Status, c.CheckID)
				}
				if outPath != "" {
					fmt.Printf("wrote %s\n", outPath)
				}
			}

			if !pcs.VerificationPassed(result) {
				printVerificationFailures(result)
				return cliExit(ExitVerificationFailed, fmt.Errorf("verification failed"))
			}
			if adm.Handoff != nil && adm.Handoff.IsLegacy() && !adm.Policy.ReleaseMode {
				fmt.Fprintln(os.Stderr, pcs.LegacyHandoffWarning)
			}
			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit VerificationResult as JSON on stdout")
	cmd.Flags().StringVar(&outPath, "out", "", "Write VerificationResult to file")
	cmd.Flags().BoolVar(&localDev, "local-dev", false, "Allow 40-zero source_commit placeholder (local development only)")
	cmd.Flags().BoolVar(&releaseMode, "release-mode", false, "Require handoff and ArtifactRegistry.v0; reject placeholder commits (or set PF_RELEASE_MODE=1)")
	cmd.Flags().StringVar(&handoffPath, "handoff", "", "HandoffManifest.v0 or legacy pf_handoff.json (required in release mode)")
	cmd.Flags().StringVar(&registryPath, "registry", "", "ArtifactRegistry.v0 for admission checks (required in release mode; defaults to PCS_CORE_PATH/examples/artifact_registry.valid.json)")
	cmd.Flags().StringVar(&manifestPath, "manifest", "", "ReleaseManifest.v0 used when writing --release-chain-result")
	cmd.Flags().StringVar(&releaseChainOut, "release-chain-result", "", "Write ReleaseChainValidationResult.v0 JSON")
	cmd.Flags().BoolVar(&allowMissingHandoff, "allow-missing-handoff-for-local-dev", false, "Allow verify without --handoff in release mode (local development only)")
	cmd.Flags().BoolVar(&allowSkippedRegistrySemantics, "allow-skipped-registry-semantics", false, "Allow registry semantic checks PF does not execute (local development only)")
	cmd.Flags().StringVar(&admissionProfileID, "admission-profile", "", "Admission profile id (e.g. labtrust.qc_release) or set PF_ADMISSION_PROFILE")
	return cmd
}
