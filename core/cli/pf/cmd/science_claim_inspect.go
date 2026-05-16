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

	cmd := &cobra.Command{
		Use:   "science-claim <signed-bundle.json>",
		Short: "Inspect a signed science claim bundle",
		Long:  `Print a human-readable summary of verification checks from a SignedScienceClaimBundle.v0 file.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			signed, err := pcs.LoadSignedScienceClaimBundle(args[0])
			if err != nil {
				return err
			}
			if err := pcs.VerifySignedBundleIntegrity(signed); err != nil {
				return fmt.Errorf("signed bundle integrity: %w", err)
			}
			opts, err := resolvePCSOpts(args[0])
			if err == nil {
				if err := pcs.ValidateSignedScienceClaimBundle(opts.RepoRoot, signed); err != nil {
					return fmt.Errorf("signed bundle schema: %w", err)
				}
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				return enc.Encode(signed.VerificationResult)
			}

			fmt.Print(pcs.FormatInspectSummary(signed))
			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit VerificationResult.v0 JSON only")
	return cmd
}
