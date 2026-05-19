// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import "github.com/spf13/cobra"

func benchmarkRootCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "benchmark",
		Short: "Run PCS admission benchmarks",
		Long:  `Measure PF release admission: valid admits, invalid rejects, failure localization, explain quality, and registry coverage.`,
	}
	cmd.AddCommand(benchmarkAdmissionCmd())
	return cmd
}
