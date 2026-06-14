// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"
)

// ReplayReport captures replay verification output for a v0.1/v0.2 bundle.
type ReplayReport struct {
	ReportID       string   `json:"report_id"`
	BundleRef      string   `json:"bundle_ref"`
	Status         string   `json:"status"`
	StaticStatus   string   `json:"static_status,omitempty"`
	ExecuteStatus  string   `json:"execute_status,omitempty"`
	KitExitCode    *int     `json:"kit_exit_code,omitempty"`
	LowViewResult  string   `json:"low_view_result,omitempty"`
	TraceFound     bool     `json:"trace_found"`
	Errors         []string `json:"errors"`
	Warnings       []string `json:"warnings"`
	ReplayedAt     string   `json:"replayed_at"`
}

// ReplayOptions configures replay verification.
type ReplayOptions struct {
	BundlePath     string
	OutPath        string
	Strict         bool
	RepoRoot       string
	BaseDir        string
	Execute        bool
	FixturesDir    string
	OutDir         string
	LowViewCompare bool
	Runner         KITRunner
}

// ReplayBundle validates a bundle and optionally executes KIT replay.
func ReplayBundle(opts ReplayOptions) (*ReplayReport, error) {
	if opts.BaseDir == "" {
		opts.BaseDir = filepath.Dir(opts.BundlePath)
	}
	if opts.RepoRoot == "" {
		if root, err := FindRepoRoot(opts.BaseDir); err == nil {
			opts.RepoRoot = root
		}
	}
	report := &ReplayReport{
		ReportID:     fmt.Sprintf("replay-%d", time.Now().UTC().UnixNano()),
		BundleRef:    filepath.ToSlash(opts.BundlePath),
		Status:       "pass",
		StaticStatus: "pass",
		Errors:       []string{},
		Warnings:     []string{},
		ReplayedAt:   time.Now().UTC().Format(time.RFC3339),
	}

	valReport, err := ValidateBundle(ValidateOptions{
		BundlePath: opts.BundlePath,
		Strict:     true,
		RepoRoot:   opts.RepoRoot,
		BaseDir:    opts.BaseDir,
	})
	if err != nil {
		report.Status = "fail"
		report.StaticStatus = "fail"
		report.Errors = append(report.Errors, valReport.Errors...)
		if len(report.Errors) == 0 {
			report.Errors = append(report.Errors, err.Error())
		}
		return report, err
	}
	report.Warnings = append(report.Warnings, valReport.Warnings...)

	data, err := os.ReadFile(opts.BundlePath)
	if err != nil {
		report.Status = "fail"
		report.StaticStatus = "fail"
		report.Errors = append(report.Errors, err.Error())
		return report, err
	}
	var bundle EvidenceBundle
	if err := json.Unmarshal(data, &bundle); err != nil {
		report.Status = "fail"
		report.StaticStatus = "fail"
		report.Errors = append(report.Errors, err.Error())
		return report, err
	}

	traceFound := false
	for _, ref := range bundle.Artifacts {
		if ref.Role != "execution-trace" {
			continue
		}
		traceFound = true
		tracePath := filepath.Join(opts.BaseDir, filepath.FromSlash(ref.Path))
		traceData, readErr := os.ReadFile(tracePath)
		if readErr != nil {
			report.Status = "fail"
			report.StaticStatus = "fail"
			report.Errors = append(report.Errors, readErr.Error())
			return report, readErr
		}
		var trace map[string]any
		if err := json.Unmarshal(traceData, &trace); err != nil {
			report.Status = "fail"
			report.StaticStatus = "fail"
			report.Errors = append(report.Errors, fmt.Sprintf("invalid execution trace JSON: %v", err))
			return report, err
		}
		expected, err := CanonicalJSONDigest(trace, "trace_digest")
		if err != nil {
			report.Status = "fail"
			report.StaticStatus = "fail"
			report.Errors = append(report.Errors, err.Error())
			return report, err
		}
		actual, _ := trace["trace_digest"].(string)
		if actual != expected {
			msg := fmt.Errorf("trace_digest mismatch: expected %s got %s", expected, actual)
			report.Status = "fail"
			report.StaticStatus = "fail"
			report.Errors = append(report.Errors, msg.Error())
			return report, msg
		}
	}
	report.TraceFound = traceFound
	if !traceFound {
		report.Warnings = append(report.Warnings, "no execution-trace artifact; replay preconditions only partially satisfied")
	}

	if opts.Execute {
		if err := runExecuteReplay(&opts, &bundle, report); err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, err.Error())
			if opts.OutPath != "" {
				_ = WriteReplayReport(opts.OutPath, report)
			}
			return report, err
		}
	}

	if opts.OutPath != "" {
		if err := WriteReplayReport(opts.OutPath, report); err != nil {
			return report, err
		}
	}
	if report.Status == "fail" {
		return report, fmt.Errorf("replay verification failed")
	}
	return report, nil
}

func runExecuteReplay(opts *ReplayOptions, bundle *EvidenceBundle, report *ReplayReport) error {
	tracePath, fixturesPath, err := resolveReplayPaths(opts, bundle)
	if err != nil {
		report.ExecuteStatus = "fail"
		return err
	}

	runner := opts.Runner
	if runner == nil {
		runner, err = NewKITRunner(opts.RepoRoot)
		if err != nil {
			report.ExecuteStatus = "fail"
			return err
		}
	}

	outDir := opts.OutDir
	if outDir == "" {
		outDir = filepath.Join(opts.BaseDir, "replay-out")
	}
	if err := os.MkdirAll(outDir, 0755); err != nil {
		report.ExecuteStatus = "fail"
		return err
	}

	certOut := filepath.Join(outDir, "replay.cert.json")
	code, err := runner.Run(tracePath, fixturesPath, certOut)
	report.KitExitCode = &code
	if err != nil {
		report.ExecuteStatus = "fail"
		return err
	}
	if code != 0 {
		report.ExecuteStatus = "fail"
		return fmt.Errorf("KIT runner exited with code %d", code)
	}
	report.ExecuteStatus = "pass"

	lowView := opts.LowViewCompare
	if bundle.ReplayContext != nil && bundle.ReplayContext.LowViewOracle {
		lowView = true
	}
	if lowView {
		certOut2 := filepath.Join(outDir, "replay2.cert.json")
		code2, err2 := runner.Run(tracePath, fixturesPath, certOut2)
		if err2 != nil {
			report.LowViewResult = "fail"
			return err2
		}
		if code2 != 0 {
			report.LowViewResult = "fail"
			return fmt.Errorf("KIT second run exited with code %d", code2)
		}
		lvCode, lvErr := runner.CompareLowView([]string{certOut, certOut2}, 99.9)
		if lvErr != nil {
			report.LowViewResult = "fail"
			return lvErr
		}
		if lvCode != 0 {
			report.LowViewResult = "fail"
			return fmt.Errorf("low-view oracle exited with code %d", lvCode)
		}
		report.LowViewResult = "pass"
	}
	return nil
}

func resolveReplayPaths(opts *ReplayOptions, bundle *EvidenceBundle) (tracePath, fixturesPath string, err error) {
	if bundle.ReplayContext != nil {
		if bundle.ReplayContext.KitTracePath != "" {
			tracePath = filepath.Join(opts.BaseDir, filepath.FromSlash(bundle.ReplayContext.KitTracePath))
		}
		if bundle.ReplayContext.FixturesPath != "" {
			fixturesPath = filepath.Join(opts.BaseDir, filepath.FromSlash(bundle.ReplayContext.FixturesPath))
		}
	}
	if opts.FixturesDir != "" {
		fixturesPath = opts.FixturesDir
	}
	if tracePath == "" {
		for _, ref := range bundle.Artifacts {
			if ref.Role == "execution-trace" {
				tracePath = filepath.Join(opts.BaseDir, filepath.FromSlash(ref.Path))
				break
			}
		}
	}
	if fixturesPath == "" {
		candidate := filepath.Join(opts.BaseDir, "fixtures")
		if st, statErr := os.Stat(candidate); statErr == nil && st.IsDir() {
			fixturesPath = candidate
		}
	}
	if tracePath == "" {
		return "", "", fmt.Errorf("no trace path resolved for execute replay")
	}
	if fixturesPath == "" {
		return "", "", fmt.Errorf("no fixtures path resolved for execute replay")
	}
	return tracePath, fixturesPath, nil
}

// WriteReplayReport writes replay report JSON.
func WriteReplayReport(path string, report *ReplayReport) error {
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	data = append(data, '\n')
	return os.WriteFile(path, data, 0644)
}
