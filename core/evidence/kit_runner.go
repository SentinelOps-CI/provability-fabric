// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
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
	// Evidence execute uses the in-tree overlay so generated certificates bind
	// to the checked-in v0.2 schema. Upstream KIT still 404s CERT-V1 schema
	// and advertises that URL as $schema; we do not treat that as success.
	return filepath.Join(r.repoRoot, "tests", "replay", "overlays", "replay_run.py")
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
		return 1, fmt.Errorf("trace replay overlay missing at %s", script)
	}
	args := []string{script, "--trace", tracePath, "--fixtures", fixturesPath}
	if certOut != "" {
		args = append(args, "--cert-out", certOut)
	}
	cmd := exec.Command(r.python(), args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Env = r.overlayPythonEnv()
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
	cmd.Env = kitPythonEnv()
	if err := cmd.Run(); err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode(), nil
		}
		return 1, err
	}
	return 0, nil
}

// kitPythonEnv returns os.Environ with PYTHONIOENCODING=utf-8 so KIT oracles
// can emit Unicode on Windows consoles that default to a legacy code page.
func kitPythonEnv() []string {
	const key = "PYTHONIOENCODING="
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, key) {
			return os.Environ()
		}
	}
	return append(os.Environ(), key+"utf-8")
}

func (r *defaultKITRunner) overlayPythonEnv() []string {
	env := kitPythonEnv()
	schema := filepath.Join(r.repoRoot, "specs", "evidence", "v0.2", "schemas", "trace-replay-cert.schema.json")
	hasSchema, hasRequired := false, false
	for _, item := range env {
		if strings.HasPrefix(item, "TRACE_REPLAY_SCHEMA_PATH=") {
			hasSchema = true
		}
		if strings.HasPrefix(item, "TRACE_REPLAY_SCHEMA_REQUIRED=") {
			hasRequired = true
		}
	}
	if !hasSchema {
		env = append(env, "TRACE_REPLAY_SCHEMA_PATH="+schema)
	}
	if !hasRequired {
		env = append(env, "TRACE_REPLAY_SCHEMA_REQUIRED=1")
	}
	return env
}
