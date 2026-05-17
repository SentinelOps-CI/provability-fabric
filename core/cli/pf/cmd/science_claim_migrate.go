// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"fmt"
	"os"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
	"github.com/spf13/cobra"
)

func migrateRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "migrate",
		Short: "Migrate PCS artifacts to pcs-core canonical shape",
		Long:  `Offline migration helpers for Proof-Carrying Science bundles. pf verify does not accept legacy input.`,
	}
	cmd.AddCommand(scienceClaimMigrateCmd())
	return cmd
}

func scienceClaimMigrateCmd() *cobra.Command {
	var outPath string

	cmd := &cobra.Command{
		Use:   "science-claim <bundle.json>",
		Short: "Migrate a legacy science claim bundle to canonical arrays",
		Long: `Convert legacy singular fields (runtime_receipt, trace_certificate) and artifact-name
schema_version values to pcs-core canonical shape (runtime_receipts[], certificates[], schema_version "v0").

Does not run verification. Use pf verify science-claim after migration.`,
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := pcs.ResolveArtifactPath(args[0])
			if err != nil {
				return err
			}
			data, err := os.ReadFile(resolved)
			if err != nil {
				return err
			}
			migrated, err := pcs.MigrateLegacyBundle(data)
			if err != nil {
				return err
			}
			if outPath == "" {
				_, _ = os.Stdout.Write(migrated)
				if len(migrated) > 0 && migrated[len(migrated)-1] != '\n' {
					_, _ = os.Stdout.Write([]byte("\n"))
				}
				return nil
			}
			outResolved, err := pcs.ResolveOutputPath(outPath)
			if err != nil {
				return err
			}
			if err := os.WriteFile(outResolved, migrated, 0644); err != nil {
				return fmt.Errorf("write migrated bundle: %w", err)
			}
			fmt.Printf("migrated bundle written to %s\n", outResolved)
			return nil
		},
	}

	cmd.Flags().StringVar(&outPath, "out", "", "Write migrated bundle to file (default: stdout)")
	return cmd
}
