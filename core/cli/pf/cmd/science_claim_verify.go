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
	return cmd
}

func scienceClaimVerifyCmd() *cobra.Command {
	var jsonOut bool
	var outPath string
	var localDev bool

	cmd := &cobra.Command{
		Use:   "science-claim <bundle.json>",
		Short: "Verify a ScienceClaimBundle.v0",
		Long:  `Run required consistency, provenance, and certificate checks on a LabTrust-certified science claim bundle.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			bundlePath := args[0]
			result, err := verifyBundle(bundlePath, localDev)
			if err != nil {
				return err
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
			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit VerificationResult as JSON on stdout")
	cmd.Flags().StringVar(&outPath, "out", "", "Write VerificationResult to file")
	cmd.Flags().BoolVar(&localDev, "local-dev", false, "Allow 40-zero source_commit placeholder (local development only)")
	return cmd
}
