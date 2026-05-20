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

func benchmarkAdmissionCmd() *cobra.Command {
	var registryPath string
	var outDir string
	var runID string
	var jsonOut bool
	var jsonSummary bool

	cmd := &cobra.Command{
		Use:   "admission",
		Short: "Run PCS release admission benchmark cases",
		Long: `Execute valid/invalid admission cases under benchmarks/admission/<workflow> and emit a pcs-core benchmark bundle (benchmark_report.v0.json, benchmark_run.v0.json, failure_localization_result.v0.json, coverage_report.v0.json, explain_quality_report.v0.json, commands.json, logs/, runs/).`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			casesDir, err := cmd.Flags().GetString("cases")
			if err != nil {
				return err
			}
			if strings.TrimSpace(casesDir) == "" {
				if len(args) == 0 {
					return fmt.Errorf("--cases is required (e.g. benchmarks/admission/labtrust_qc_release)")
				}
				casesDir = args[0]
			}
			resolvedCases, err := pcs.ResolveDirectoryPath(casesDir)
			if err != nil {
				return err
			}
			repoRoot := ""
			if wd, wdErr := os.Getwd(); wdErr == nil {
				repoRoot, _ = pcs.FindRepoRoot(wd)
			}
			if repoRoot == "" {
				repoRoot, _ = pcs.FindRepoRoot(resolvedCases)
			}
			regPath := strings.TrimSpace(registryPath)
			if regPath == "" {
				if def, ok := pcs.DefaultArtifactRegistryPath(); ok {
					regPath = def
				}
			} else if resolved, rErr := pcs.ResolveArtifactPath(regPath); rErr == nil {
				regPath = resolved
			}
			out := strings.TrimSpace(outDir)
			if out == "" {
				workflowName := filepath.Base(resolvedCases)
				out = filepath.Join(repoRoot, "benchmark_runs", workflowName+"_admission")
			} else if resolved, oErr := pcs.ResolveBenchmarkOutputDir(out); oErr == nil {
				out = resolved
			}
			sourceCommit, err := pcs.ResolveSourceCommitForMode(true, false)
			if err != nil {
				return err
			}
			run, loc, cov, explain, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
				RepoRoot:         repoRoot,
				CasesDir:         resolvedCases,
				RegistryPath:     regPath,
				SourceCommit:     sourceCommit,
				ValidatorVersion: pcs.DefaultVerifierVersion,
				OutDir:           out,
				RunID:            runID,
			})
			if err != nil {
				return err
			}
			if jsonSummary {
				raw, mErr := pcs.FormatBenchmarkAdmissionSummaryJSON(run, out)
				if mErr != nil {
					return mErr
				}
				fmt.Print(raw)
			} else if jsonOut {
				raw, mErr := pcs.FormatExplainReportJSON(run)
				if mErr != nil {
					return mErr
				}
				fmt.Print(raw)
			} else {
				fmt.Printf("run_id: %s\n", run.RunID)
				fmt.Printf("workflow: %s\n", run.Workflow)
				fmt.Printf("valid_release_admission_rate: %.3f\n", run.Metrics.ValidReleaseAdmissionRate)
				fmt.Printf("invalid_release_rejection_rate: %.3f\n", run.Metrics.InvalidReleaseRejectionRate)
				fmt.Printf("failure_localization_accuracy: %.3f\n", run.Metrics.FailureLocalizationAccuracy)
				fmt.Printf("failure_code_accuracy: %.3f\n", run.Metrics.FailureCodeAccuracy)
				fmt.Printf("explain_output_completeness: %.3f\n", run.Metrics.ExplainOutputCompleteness)
				fmt.Printf("registry_check_coverage: %.3f\n", run.Metrics.RegistryCheckCoverage)
				fmt.Printf("admission_profile_coverage: %.3f\n", run.Metrics.AdmissionProfileCoverage)
				fmt.Printf("formal_check_enforcement_coverage: %.3f\n", run.Metrics.FormalCheckEnforcementCoverage)
				fmt.Printf("wrote %s\n", out)
			}
			failed := 0
			for _, c := range run.Cases {
				if !c.Passed {
					failed++
				}
			}
			if failed > 0 {
				return cliExit(ExitVerificationFailed, fmt.Errorf("%d/%d benchmark cases failed", failed, len(run.Cases)))
			}
			_ = loc
			_ = cov
			_ = explain
			return nil
		},
	}
	cmd.Flags().String("cases", "", "Benchmark case directory (e.g. benchmarks/admission/labtrust_qc_release)")
	cmd.Flags().StringVar(&registryPath, "registry", "", "ArtifactRegistry.v0 path (defaults to PCS_CORE_PATH/examples/artifact_registry.valid.json)")
	cmd.Flags().StringVar(&outDir, "out", "", "Output directory for benchmark_run.v0.json and related reports")
	cmd.Flags().StringVar(&runID, "run-id", "", "Optional benchmark run id")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Emit admission_benchmark_suite.v0.json on stdout (legacy)")
	cmd.Flags().BoolVar(&jsonSummary, "json-summary", false, "Emit compact JSON summary on stdout")
	return cmd
}
