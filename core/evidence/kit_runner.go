// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
)

// KITRunner executes TRACE-REPLAY-KIT replay_run.py.
type KITRunner interface {
	Run(tracePath, fixturesPath, certOut string) (exitCode int, err error)
	CompareLowView(outputFiles []string, minDeterminism float64) (exitCode int, err error)
}

type defaultKITRunner struct {
	repoRoot string
}

// NewKITRunner returns a runner rooted at repoRoot (or discovered from cwd).
func NewKITRunner(repoRoot string) (KITRunner, error) {
	if repoRoot == "" {
		var err error
		repoRoot, err = FindRepoRoot(".")
		if err != nil {
			return nil, err
		}
	}
	return &defaultKITRunner{repoRoot: repoRoot}, nil
}

func (r *defaultKITRunner) python() string {
	candidates := []string{"python3", "python"}
	if runtime.GOOS == "windows" {
		candidates = []string{"python", "py", "python3"}
	}
	for _, name := range candidates {
		if _, err := exec.LookPath(name); err == nil {
			return name
		}
	}
	return "python3"
}

func (r *defaultKITRunner) runnerScript() string {
	return filepath.Join(r.repoRoot, "external", "TRACE-REPLAY-KIT", "runner", "replay_run.py")
}

func (r *defaultKITRunner) lowViewOracle() string {
	return filepath.Join(r.repoRoot, "external", "TRACE-REPLAY-KIT", "oracles", "lowview_equal.py")
}

// RunKITTrace executes the KIT runner and returns process exit code.
func RunKITTrace(tracePath, fixturesPath, outDir, repoRoot string) (int, error) {
	runner, err := NewKITRunner(repoRoot)
	if err != nil {
		return 1, err
	}
	certOut := filepath.Join(outDir, "replay.cert.json")
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return 1, err
	}
	return runner.Run(tracePath, fixturesPath, certOut)
}

func (r *defaultKITRunner) Run(tracePath, fixturesPath, certOut string) (int, error) {
	script := r.runnerScript()
	if _, err := os.Stat(script); err != nil {
		return 1, fmt.Errorf("KIT runner missing at %s (run make submodules)", script)
	}
	args := []string{script, "--trace", tracePath, "--fixtures", fixturesPath}
	if certOut != "" {
		args = append(args, "--cert-out", certOut)
	}
	cmd := exec.Command(r.python(), args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode(), nil
		}
		return 1, err
	}
	return 0, nil
}

func (r *defaultKITRunner) CompareLowView(outputFiles []string, minDeterminism float64) (int, error) {
	oracle := r.lowViewOracle()
	if _, err := os.Stat(oracle); err != nil {
		return 1, fmt.Errorf("low-view oracle missing at %s", oracle)
	}
	if len(outputFiles) < 2 {
		return 1, fmt.Errorf("low-view compare requires at least two output files")
	}
	args := append([]string{oracle, "--min-determinism", fmt.Sprintf("%.6f", minDeterminism)}, outputFiles...)
	cmd := exec.Command(r.python(), args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode(), nil
		}
		return 1, err
	}
	return 0, nil
}
