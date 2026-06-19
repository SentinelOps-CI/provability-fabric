// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/spf13/cobra"
)

func pfCoreCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "core",
		Short: "PF-Core validator commands (compile-observation, check-trace, emit-certificate, emit-artifacts)",
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(args)
		},
	}
	cmd.AddCommand(&cobra.Command{
		Use:                "compile-observation",
		Short:              "Compile runtime_observation.v1 to event.v1",
		DisableFlagParsing: true,
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(append([]string{"core", "compile-observation"}, args...))
		},
	})
	cmd.AddCommand(&cobra.Command{
		Use:                "check-trace",
		Short:              "Validate trace hash chain and safety deciders",
		DisableFlagParsing: true,
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(append([]string{"core", "check-trace"}, args...))
		},
	})
	cmd.AddCommand(&cobra.Command{
		Use:                "emit-certificate",
		Short:              "Emit pf-core.certificate.v0 for a trace",
		DisableFlagParsing: true,
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(append([]string{"core", "emit-certificate"}, args...))
		},
	})
	cmd.AddCommand(&cobra.Command{
		Use:                "emit-artifacts",
		Short:              "Emit five-file PF-Core artifact bundle",
		DisableFlagParsing: true,
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(append([]string{"core", "emit-artifacts"}, args...))
		},
	})
	cmd.AddCommand(&cobra.Command{
		Use:                "schema-check",
		Short:              "Validate PF-Core JSON schemas",
		DisableFlagParsing: true,
		RunE: func(cmd *cobra.Command, args []string) error {
			return runPfCoreCLI(append([]string{"core", "schema-check"}, args...))
		},
	})
	return cmd
}

func runPfCoreCLI(args []string) error {
	root, err := repoRoot()
	if err != nil {
		return err
	}
	script := filepath.Join(root, "scripts", "pf-core.sh")
	if _, err := os.Stat(script); err != nil {
		return fmt.Errorf("pf-core wrapper script missing: %w", err)
	}
	pyArgs := append([]string{script}, args...)
	proc := exec.Command("bash", pyArgs...)
	proc.Stdout = os.Stdout
	proc.Stderr = os.Stderr
	proc.Stdin = os.Stdin
	if err := proc.Run(); err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			os.Exit(exitErr.ExitCode())
		}
		return err
	}
	return nil
}

func repoRoot() (string, error) {
	wd, err := os.Getwd()
	if err != nil {
		return "", err
	}
	dir := wd
	for {
		if _, err := os.Stat(filepath.Join(dir, "scripts", "pf-core.sh")); err == nil {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return wd, nil
		}
		dir = parent
	}
}
