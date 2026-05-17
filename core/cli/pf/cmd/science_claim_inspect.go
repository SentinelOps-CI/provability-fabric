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

func inspectRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "inspect",
		Short: "Inspect PCS artifacts",
		Long:  `Inspect signed or verified Proof-Carrying Science artifacts.`,
	}
	cmd.AddCommand(scienceClaimInspectCmd())
	return cmd
}

func scienceClaimInspectCmd() *cobra.Command {
	var jsonOut bool
	var strictDigests bool
	var reverify bool

	cmd := &cobra.Command{
		Use:   "science-claim <signed-bundle.json>",
		Short: "Inspect a signed science claim bundle",
		Long: `Print a human-readable summary of verification checks from a SignedScienceClaimBundle.v0 file.

By default, inspect validates the pcs-core schema and embedded verification status without requiring
PF-computed digests (so LabTrust-exported signed bundles load cleanly). Use --strict to require PF digest
alignment. Use --reverify to run the full 15-check PF verifier on the embedded science_claim_bundle.`,
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			signed, err := pcs.LoadSignedScienceClaimBundle(args[0])
			if err != nil {
				return err
			}
			opts, err := resolvePCSOpts(args[0], false, false)
			if err != nil {
				return err
			}
			if err := pcs.ValidateSignedScienceClaimBundle(opts.RepoRoot, signed); err != nil {
				return fmt.Errorf("signed bundle schema: %w", err)
			}
			if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: strictDigests}); err != nil {
				return fmt.Errorf("signed bundle integrity: %w", err)
			}

			var fresh *pcs.VerificationResult
			if reverify && signed.ScienceClaimBundle != nil {
				opts.VerifierVersion = pcs.DefaultVerifierVersion
				if opts.SourceCommit == "" {
					opts.SourceCommit = pcs.ResolveSourceCommit()
				}
				r, err := pcs.VerifyScienceClaimBundleValue(signed.ScienceClaimBundle, opts)
				if err != nil {
					return fmt.Errorf("reverify: %w", err)
				}
				fresh = &r
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				if fresh != nil {
					if err := enc.Encode(map[string]any{
						"embedded":   signed.VerificationResult,
						"reverified": fresh,
					}); err != nil {
						return err
					}
				} else if err := enc.Encode(signed.VerificationResult); err != nil {
					return err
				}
			} else {
				fmt.Print(pcs.FormatInspectSummaryWithReverify(signed, fresh))
			}

			if fresh != nil && !pcs.VerificationPassed(*fresh) {
				printVerificationFailures(*fresh)
				return cliExit(ExitVerificationFailed, fmt.Errorf("reverification failed: status %s", fresh.Status))
			}
			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit VerificationResult JSON (embedded only, or embedded+reverified with --reverify)")
	cmd.Flags().BoolVar(&strictDigests, "strict", false, "Require PF-computed verification_result and wrapper digests")
	cmd.Flags().BoolVar(&reverify, "reverify", false, "Re-run PF 15-check verification on embedded science_claim_bundle")
	return cmd
}
