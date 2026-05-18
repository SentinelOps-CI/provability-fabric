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
	return &cobra.Command{
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
			fmt.Println(pcs.FormatFailureExplanations(explanations))
			return cliExit(ExitVerificationFailed, fmt.Errorf("verification result contains %d failed check(s)", len(explanations)))
		},
	}
}

func explainReleaseChainCmd() *cobra.Command {
	return &cobra.Command{
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
			explanations := pcs.ExplainReleaseChainFailures(result)
			if len(explanations) == 0 {
				fmt.Printf("OK: no failed checks in %s (status=%s)\n", resolved, result.Status)
				return nil
			}
			fmt.Println(pcs.FormatFailureExplanations(explanations))
			return cliExit(ExitVerificationFailed, fmt.Errorf("release chain result contains %d failed check(s)", len(explanations)))
		},
	}
}
