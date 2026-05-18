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

func explainRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "explain",
		Short: "Explain PCS verification failures",
	}
	cmd.AddCommand(explainFailureCmd())
	cmd.AddCommand(explainReleaseChainCmd())
	return cmd
}

func explainFailureCmd() *cobra.Command {
	var jsonOut bool
	cmd := &cobra.Command{
		Use:   "failure <verification_result.json>",
		Short: "Explain failed checks in a VerificationResult.v0",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := pcs.ResolveArtifactPath(args[0])
			if err != nil {
				return err
			}
			data, err := os.ReadFile(resolved)
			if err != nil {
				return err
			}
			var result pcs.VerificationResult
			if err := json.Unmarshal(data, &result); err != nil {
				return fmt.Errorf("parse: %w", err)
			}
			explanations := pcs.ExplainVerificationFailures(result)
			if len(explanations) == 0 {
				fmt.Printf("OK: no failed checks in %s (status=%s)\n", resolved, result.Status)
				return nil
			}
			if jsonOut {
				out, err := pcs.FormatExplainReportJSON(map[string]any{
					"status":        result.Status,
					"failed":        explanations,
					"failed_count":  len(explanations),
				})
				if err != nil {
					return err
				}
				fmt.Print(out)
			} else {
				fmt.Println(pcs.FormatFailureExplanationsOperational(explanations))
			}
			return cliExit(ExitVerificationFailed, fmt.Errorf("verification result contains %d failed check(s)", len(explanations)))
		},
	}
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit structured JSON explain report")
	return cmd
}

func explainReleaseChainCmd() *cobra.Command {
	var jsonOut bool
	cmd := &cobra.Command{
		Use:   "release-chain <release_chain_validation_result.json>",
		Short: "Explain failed checks in a ReleaseChainValidationResult.v0",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := pcs.ResolveArtifactPath(args[0])
			if err != nil {
				return err
			}
			data, err := os.ReadFile(resolved)
			if err != nil {
				return err
			}
			var result pcs.ReleaseChainValidationResult
			if err := json.Unmarshal(data, &result); err != nil {
				return fmt.Errorf("parse: %w", err)
			}
			report := pcs.BuildExplainReleaseChainReport(result)
			if report.FailedCount == 0 && report.DeferredCount == 0 {
				fmt.Printf("OK: no failed or deferred registry checks in %s (status=%s)\n", resolved, result.Status)
				return nil
			}
			if jsonOut {
				out, err := pcs.FormatExplainReportJSON(report)
				if err != nil {
					return err
				}
				fmt.Print(out)
			} else {
				if len(report.Failed) > 0 {
					fmt.Println(pcs.FormatFailureExplanationsOperational(report.Failed))
				}
				if len(report.Deferred) > 0 {
					if len(report.Failed) > 0 {
						fmt.Println()
					}
					fmt.Println("Deferred registry checks (informational):")
					fmt.Println(pcs.FormatFailureExplanationsOperational(report.Deferred))
				}
			}
			if report.FailedCount > 0 {
				return cliExit(ExitVerificationFailed, fmt.Errorf("release chain result contains %d failed check(s)", report.FailedCount))
			}
			return nil
		},
	}
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit structured JSON explain report")
	return cmd
}
