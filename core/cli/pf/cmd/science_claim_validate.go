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

func validateRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "validate",
		Short: "Validate PCS artifacts against pcs-core JSON Schema",
		Long:  `Schema-validate science claim bundles, verification results, and signed wrappers.`,
	}
	cmd.AddCommand(validateScienceClaimBundleCmd())
	cmd.AddCommand(validateVerificationResultCmd())
	cmd.AddCommand(validateSignedScienceClaimCmd())
	return cmd
}

func validateScienceClaimBundleCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "science-claim <bundle.json>",
		Short: "Validate a ScienceClaimBundle.v0 file",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := pcs.ResolveArtifactPath(args[0])
			if err != nil {
				return err
			}
			bundle, err := pcs.LoadScienceClaimBundle(resolved)
			if err != nil {
				return err
			}
			opts, err := resolvePCSOpts(resolved, false)
			if err != nil {
				return err
			}
			if err := pcs.ValidateScienceClaimBundleValue(opts.RepoRoot, bundle); err != nil {
				return fmt.Errorf("schema: %w", err)
			}
			fmt.Printf("OK: %s (schema valid)\n", resolved)
			return nil
		},
	}
}

func validateVerificationResultCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "verification-result <result.json>",
		Short: "Validate a VerificationResult.v0 file",
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
			opts, err := resolvePCSOpts(resolved, false)
			if err != nil {
				return err
			}
			if err := pcs.ValidateVerificationResult(opts.RepoRoot, result); err != nil {
				return fmt.Errorf("schema: %w", err)
			}
			fmt.Printf("OK: %s (schema valid, status=%s)\n", resolved, result.Status)
			return nil
		},
	}
}

func validateSignedScienceClaimCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "signed-science-claim <signed.json>",
		Short: "Validate a SignedScienceClaimBundle.v0 file",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := pcs.ResolveArtifactPath(args[0])
			if err != nil {
				return err
			}
			signed, err := pcs.LoadSignedScienceClaimBundle(resolved)
			if err != nil {
				return err
			}
			opts, err := resolvePCSOpts(resolved, false)
			if err != nil {
				return err
			}
			if err := pcs.ValidateSignedScienceClaimBundle(opts.RepoRoot, signed); err != nil {
				return fmt.Errorf("schema: %w", err)
			}
			fmt.Printf("OK: %s (schema valid)\n", resolved)
			return nil
		},
	}
}
