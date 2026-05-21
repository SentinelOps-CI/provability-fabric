// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
	"github.com/spf13/cobra"
)

func registerBenchmarkValidateCommands(validate *cobra.Command) {
	validate.AddCommand(validateBenchmarkArtifactCmd())
	validate.AddCommand(validateBenchmarkBundleCmd())
}

func validateBenchmarkArtifactCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "benchmark-artifact <path.json>",
		Short: "Validate a pcs-core benchmark bundle JSON file",
		Long:  `Schema-validate benchmark_report.v0.json, coverage_report.v0.json, explain_quality_report.v0.json, or pcs_bench_ingest.v0.json (array or object).`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			path := args[0]
			if !filepath.IsAbs(path) {
				if wd, err := os.Getwd(); err == nil {
					path = filepath.Join(wd, path)
				}
			}
			repoRoot, _ := pcs.FindRepoRoot(path)
			if err := pcs.ValidateBenchmarkArtifactFile(repoRoot, path); err != nil {
				return err
			}
			fmt.Printf("OK: %s\n", path)
			return nil
		},
	}
}

func validateBenchmarkBundleCmd() *cobra.Command {
	var pcsCoreRoot string
	cmd := &cobra.Command{
		Use:   "benchmark-bundle <dir>",
		Short: "Validate a full pf benchmark admission output directory",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			dir := args[0]
			if !filepath.IsAbs(dir) {
				if wd, err := os.Getwd(); err == nil {
					dir = filepath.Join(wd, dir)
				}
			}
			repoRoot, _ := pcs.FindRepoRoot(dir)
			pcsCore := strings.TrimSpace(pcsCoreRoot)
			if pcsCore != "" {
				if resolved, err := pcs.ResolveArtifactPath(pcsCore); err == nil {
					pcsCore = resolved
				}
				if err := pcs.ValidateBenchmarkBundleArtifactsWithPCSCore(repoRoot, pcsCore, dir); err != nil {
					return err
				}
				fmt.Printf("OK: benchmark bundle %s (pcs-core schemas)\n", dir)
				return nil
			}
			if err := pcs.ValidateBenchmarkBundleArtifacts(repoRoot, dir); err != nil {
				return err
			}
			fmt.Printf("OK: benchmark bundle %s\n", dir)
			return nil
		},
	}
	cmd.Flags().StringVar(&pcsCoreRoot, "pcs-core", "", "Validate against pcs-core/schemas (path to pcs-core checkout)")
	return cmd
}
