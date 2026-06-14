// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"encoding/json"
	"fmt"
	"os"

	evidence "github.com/SentinelOps-CI/provability-fabric/core/evidence"
	"github.com/spf13/cobra"
)

func evidenceCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "evidence",
		Short: "Evidence v0.1 bundle pack, validate, trace import, and replay",
		Long:  "Pack, validate, and replay Evidence v0.1 JSON bundles (distinct from PCS EvidenceBundle.v0 and so bundle pack tar archives).",
	}
	cmd.AddCommand(evidenceBundleCmd())
	cmd.AddCommand(evidenceValidateCmd())
	cmd.AddCommand(evidenceTraceCmd())
	cmd.AddCommand(evidenceReplayCmd())
	return cmd
}

func evidenceTraceCmd() *cobra.Command {
	var kitPath, outPath, traceID string
	cmd := &cobra.Command{
		Use:   "trace",
		Short: "Execution trace operations",
	}
	importCmd := &cobra.Command{
		Use:   "import",
		Short: "Import TRACE-REPLAY-KIT trace JSON into v0.1 execution-trace",
		RunE: func(cmd *cobra.Command, args []string) error {
			if kitPath == "" || outPath == "" {
				return fmt.Errorf("--kit-trace and --out are required")
			}
			trace, err := evidence.ImportKITTrace(kitPath, traceID)
			if err != nil {
				return err
			}
			if err := evidence.WriteExecutionTrace(outPath, trace); err != nil {
				return err
			}
			fmt.Printf("Wrote execution trace %s (digest %s)\n", outPath, trace.TraceDigest)
			return nil
		},
	}
	importCmd.Flags().StringVar(&kitPath, "kit-trace", "", "Path to TRACE-REPLAY-KIT trace.json")
	importCmd.Flags().StringVar(&outPath, "out", "", "Output execution-trace.json path")
	importCmd.Flags().StringVar(&traceID, "trace-id", "", "Optional trace_id (default from kit name)")
	_ = importCmd.MarkFlagRequired("kit-trace")
	_ = importCmd.MarkFlagRequired("out")
	cmd.AddCommand(importCmd)
	return cmd
}

func evidenceBundleCmd() *cobra.Command {
	var manifestPath, outPath string
	var jsonOut bool

	bundle := &cobra.Command{
		Use:   "bundle",
		Short: "Evidence v0.1 bundle operations",
	}
	pack := &cobra.Command{
		Use:   "pack",
		Short: "Pack an Evidence v0.1 bundle from a manifest",
		RunE: func(cmd *cobra.Command, args []string) error {
			if manifestPath == "" || outPath == "" {
				return fmt.Errorf("--manifest and --out are required")
			}
			b, err := evidence.Pack(evidence.PackOptions{
				ManifestPath: manifestPath,
				OutPath:      outPath,
			})
			if err != nil {
				return err
			}
			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				return enc.Encode(b)
			}
			fmt.Printf("Wrote bundle %s (digest %s)\n", outPath, b.BundleDigest)
			return nil
		},
	}
	pack.Flags().StringVar(&manifestPath, "manifest", "", "Path to pack manifest JSON")
	pack.Flags().StringVar(&outPath, "out", "", "Output bundle JSON path")
	pack.Flags().BoolVar(&jsonOut, "json", false, "Emit packed bundle JSON to stdout")
	_ = pack.MarkFlagRequired("manifest")
	_ = pack.MarkFlagRequired("out")
	bundle.AddCommand(pack)
	return bundle
}

func evidenceValidateCmd() *cobra.Command {
	var strict bool
	var reportOut string
	var jsonOut bool
	var baseDir string

	cmd := &cobra.Command{
		Use:   "validate [bundle]",
		Short: "Validate an Evidence v0.1 bundle",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			report, err := evidence.ValidateBundle(evidence.ValidateOptions{
				BundlePath: args[0],
				Strict:     strict,
				BaseDir:    baseDir,
			})
			if report == nil {
				return err
			}
			if reportOut != "" {
				if writeErr := evidence.WriteValidationReport(reportOut, report); writeErr != nil {
					return writeErr
				}
			}
			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(report)
			} else if err != nil {
				fmt.Printf("status: %s\n", report.Status)
				for _, msg := range report.Errors {
					fmt.Printf("error: %s\n", msg)
				}
			} else {
				fmt.Printf("Validation passed: %s\n", args[0])
			}
			if err != nil {
				return err
			}
			return nil
		},
	}
	cmd.Flags().BoolVar(&strict, "strict", false, "Fail closed on schema, digest, and cross-ref errors")
	cmd.Flags().StringVar(&baseDir, "base-dir", "", "Directory containing artifact paths (default: bundle directory)")
	cmd.Flags().StringVar(&reportOut, "report-out", "", "Write validation report JSON")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit validation report JSON to stdout")
	return cmd
}

func evidenceReplayCmd() *cobra.Command {
	var outPath string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "replay",
		Short: "Verify replay preconditions for an Evidence v0.1 bundle",
		RunE: func(cmd *cobra.Command, args []string) error {
			bundlePath, _ := cmd.Flags().GetString("bundle")
			if bundlePath == "" {
				return fmt.Errorf("--bundle is required")
			}
			report, err := evidence.ReplayBundle(evidence.ReplayOptions{
				BundlePath: bundlePath,
				OutPath:    outPath,
			})
			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(report)
			} else {
				fmt.Printf("status: %s trace_found=%v\n", report.Status, report.TraceFound)
				for _, msg := range report.Errors {
					fmt.Printf("error: %s\n", msg)
				}
			}
			return err
		},
	}
	cmd.Flags().String("bundle", "", "Path to Evidence v0.1 bundle JSON")
	_ = cmd.MarkFlagRequired("bundle")
	cmd.Flags().StringVar(&outPath, "out", "", "Write replay report JSON")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit replay report JSON to stdout")
	return cmd
}
