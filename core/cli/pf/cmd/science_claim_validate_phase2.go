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

func registerPhase2ValidateCommands(validate *cobra.Command) {
	validate.AddCommand(validateHandoffManifestCmd())
	validate.AddCommand(validateReleaseManifestCmd())
	validate.AddCommand(validateArtifactRegistryCmd())
	validate.AddCommand(validateReleaseChainResultCmd())
}

func validateHandoffManifestCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "handoff-manifest <handoff.json>",
		Short: "Validate a HandoffManifest.v0 file",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if err := pcs.ValidateHandoffManifestFile("", args[0]); err != nil {
				return err
			}
			fmt.Printf("OK: %s (HandoffManifest.v0 schema valid)\n", args[0])
			return nil
		},
	}
}

func validateArtifactRegistryCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "artifact-registry <registry.json>",
		Short: "Validate an ArtifactRegistry.v0 file",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if err := pcs.ValidateArtifactRegistryFile("", args[0]); err != nil {
				return err
			}
			fmt.Printf("OK: %s (ArtifactRegistry.v0 schema valid)\n", args[0])
			return nil
		},
	}
}

func validateReleaseManifestCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "release-manifest <manifest.json>",
		Short: "Validate a ReleaseManifest.v0 file",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if err := pcs.ValidateReleaseManifestFile("", args[0]); err != nil {
				return err
			}
			fmt.Printf("OK: %s (ReleaseManifest.v0 schema valid)\n", args[0])
			return nil
		},
	}
}

func validateReleaseChainResultCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "release-chain-result <result.json>",
		Short: "Validate a ReleaseChainValidationResult.v0 file",
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
			if err := pcs.ValidateReleaseChainValidationResult("", result); err != nil {
				return err
			}
			fmt.Printf("OK: %s (ReleaseChainValidationResult.v0 schema valid, status=%s)\n", resolved, result.Status)
			return nil
		},
	}
}
