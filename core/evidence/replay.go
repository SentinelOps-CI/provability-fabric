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

// ReplayReport captures replay verification output for a v0.1 bundle.
type ReplayReport struct {
	ReportID    string   `json:"report_id"`
	BundleRef   string   `json:"bundle_ref"`
	Status      string   `json:"status"`
	TraceFound  bool     `json:"trace_found"`
	Errors      []string `json:"errors"`
	Warnings    []string `json:"warnings"`
	ReplayedAt  string   `json:"replayed_at"`
}

// ReplayOptions configures replay verification.
type ReplayOptions struct {
	BundlePath string
	OutPath    string
	Strict     bool
	RepoRoot   string
	BaseDir    string
}

// ReplayBundle validates a bundle and verifies replay preconditions for execution traces.
func ReplayBundle(opts ReplayOptions) (*ReplayReport, error) {
	if opts.BaseDir == "" {
		opts.BaseDir = filepath.Dir(opts.BundlePath)
	}
	report := &ReplayReport{
		ReportID:   fmt.Sprintf("replay-%d", time.Now().UTC().UnixNano()),
		BundleRef:  filepath.ToSlash(opts.BundlePath),
		Status:     "pass",
		Errors:     []string{},
		Warnings:   []string{},
		ReplayedAt: time.Now().UTC().Format(time.RFC3339),
	}

	valReport, err := ValidateBundle(ValidateOptions{
		BundlePath: opts.BundlePath,
		Strict:     true,
		RepoRoot:   opts.RepoRoot,
		BaseDir:    opts.BaseDir,
	})
	if err != nil {
		report.Status = "fail"
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
		report.Errors = append(report.Errors, err.Error())
		return report, err
	}
	var bundle EvidenceBundle
	if err := json.Unmarshal(data, &bundle); err != nil {
		report.Status = "fail"
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
			report.Errors = append(report.Errors, readErr.Error())
			return report, readErr
		}
		var trace map[string]any
		if err := json.Unmarshal(traceData, &trace); err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, fmt.Sprintf("invalid execution trace JSON: %v", err))
			return report, err
		}
		expected, err := CanonicalJSONDigest(trace, "trace_digest")
		if err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, err.Error())
			return report, err
		}
		actual, _ := trace["trace_digest"].(string)
		if actual != expected {
			msg := fmt.Errorf("trace_digest mismatch: expected %s got %s", expected, actual)
			report.Status = "fail"
			report.Errors = append(report.Errors, msg.Error())
			return report, msg
		}
	}
	report.TraceFound = traceFound
	if !traceFound {
		report.Warnings = append(report.Warnings, "no execution-trace artifact; replay preconditions only partially satisfied")
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

// WriteReplayReport writes replay report JSON.
func WriteReplayReport(path string, report *ReplayReport) error {
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	data = append(data, '\n')
	return os.WriteFile(path, data, 0644)
}
