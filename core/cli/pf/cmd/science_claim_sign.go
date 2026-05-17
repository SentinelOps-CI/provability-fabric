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

func scienceClaimSignCmd() *cobra.Command {
	var outPath string
	var jsonOut bool
	var localDev bool

	cmd := &cobra.Command{
		Use:   "science-claim <bundle.json>",
		Short: "Sign a verified ScienceClaimBundle.v0",
		Long:  `Verify the bundle and emit a SignedScienceClaimBundle.v0 wrapper for Scientific Memory import. Signing is refused unless verification passes.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			bundlePath := args[0]
			if outPath == "" {
				return fmt.Errorf("--out is required")
			}
			outResolved, err := pcs.ResolveOutputPath(outPath)
			if err != nil {
				return err
			}
			resolved, err := pcs.ResolveArtifactPath(bundlePath)
			if err != nil {
				return err
			}
			bundle, err := pcs.LoadScienceClaimBundle(resolved)
			if err != nil {
				return err
			}
			opts, err := resolvePCSOpts(resolved, localDev)
			if err != nil {
				return err
			}
			result, err := pcs.VerifyScienceClaimBundle(resolved, bundle, opts)
			if err != nil {
				return err
			}
			if !pcs.VerificationPassed(result) {
				printVerificationFailures(result)
				return cliExit(ExitVerificationFailed, fmt.Errorf("signing refused: verification status is %s", result.Status))
			}

			signed, err := pcs.SignVerificationResult(opts.RepoRoot, bundle, result)
			if err != nil {
				return err
			}

			data, err := json.MarshalIndent(signed, "", "  ")
			if err != nil {
				return err
			}
			if err := os.WriteFile(outResolved, data, 0644); err != nil {
				return fmt.Errorf("write signed bundle: %w", err)
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(signed)
			} else {
				fmt.Printf("signed bundle written to %s\n", outResolved)
				fmt.Printf("signed_bundle_id: %s\n", signed.SignedBundleID)
				fmt.Printf("verification_id: %s\n", result.VerificationID)
				fmt.Printf("status: %s\n", result.Status)
			}
			return nil
		},
	}

	cmd.Flags().StringVar(&outPath, "out", "", "Output path for signed_science_claim_bundle.json")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Also print signed wrapper JSON to stdout")
	cmd.Flags().BoolVar(&localDev, "local-dev", false, "Allow 40-zero source_commit placeholder (local development only)")
	_ = cmd.MarkFlagRequired("out")
	return cmd
}
