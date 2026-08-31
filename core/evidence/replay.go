// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"time"
)

// ReplayReport captures replay verification output for a v0.1/v0.2 bundle.
type ReplayReport struct {
	ReportID             string   `json:"report_id"`
	BundleRef            string   `json:"bundle_ref"`
	Status               string   `json:"status"`
	StaticStatus         string   `json:"static_status,omitempty"`
	ExecuteStatus        string   `json:"execute_status,omitempty"`
	KitExitCode          *int     `json:"kit_exit_code,omitempty"`
	KitSecondExitCode    *int     `json:"kit_second_exit_code,omitempty"`
	LowViewResult        string   `json:"low_view_result,omitempty"`
	ReplayCertValidation string   `json:"replay_cert_validation,omitempty"`
	ReplayCertSchema     string   `json:"replay_cert_schema,omitempty"`
	ReplayArtifacts      []string `json:"replay_artifacts,omitempty"`
	TraceFound           bool     `json:"trace_found"`
	Errors               []string `json:"errors"`
	Warnings             []string `json:"warnings"`
	ReplayedAt           string   `json:"replayed_at"`
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
		tracePath, pathErr := resolveContainedExistingPath(opts.BaseDir, ref.Path)
		if pathErr != nil {
			report.Status = "fail"
			report.StaticStatus = "fail"
			report.Errors = append(report.Errors, pathErr.Error())
			return report, pathErr
		}
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
	report.ReplayCertSchema = "specs/evidence/v0.2/schemas/trace-replay-cert.schema.json"
	if err := validateTraceReplayCert(opts.RepoRoot, certOut, tracePath, fixturesPath); err != nil {
		report.ExecuteStatus = "fail"
		report.ReplayCertValidation = "fail"
		return err
	}
	report.ReplayArtifacts = append(report.ReplayArtifacts, filepath.Base(certOut))
	report.ReplayCertValidation = "pass"
	report.ExecuteStatus = "pass"

	lowView := opts.LowViewCompare
	if bundle.ReplayContext != nil && bundle.ReplayContext.LowViewOracle {
		lowView = true
	}
	if lowView {
		certOut2 := filepath.Join(outDir, "replay2.cert.json")
		code2, err2 := runner.Run(tracePath, fixturesPath, certOut2)
		report.KitSecondExitCode = &code2
		if err2 != nil {
			report.LowViewResult = "fail"
			report.ReplayCertValidation = "fail"
			return err2
		}
		if code2 != 0 {
			report.LowViewResult = "fail"
			report.ReplayCertValidation = "fail"
			return fmt.Errorf("KIT second run exited with code %d", code2)
		}
		if err := validateTraceReplayCert(opts.RepoRoot, certOut2, tracePath, fixturesPath); err != nil {
			report.LowViewResult = "fail"
			report.ReplayCertValidation = "fail"
			return err
		}
		report.ReplayArtifacts = append(report.ReplayArtifacts, filepath.Base(certOut2))
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

func validateTraceReplayCert(repoRoot, certPath, tracePath, fixturesPath string) error {
	if repoRoot == "" {
		root, err := FindRepoRoot(".")
		if err != nil {
			return fmt.Errorf("resolve repository root for trace replay certificate validation: %w", err)
		}
		repoRoot = root
	}
	body, err := os.ReadFile(certPath)
	if err != nil {
		return fmt.Errorf("read trace replay certificate %s: %w", filepath.Base(certPath), err)
	}
	schemaPath := filepath.Join(
		repoRoot,
		"specs", "evidence", "v0.2", "schemas", "trace-replay-cert.schema.json",
	)
	if err := validateAgainstSchema(schemaPath, body); err != nil {
		return fmt.Errorf("trace replay certificate %s failed local schema validation: %w", filepath.Base(certPath), err)
	}

	var cert struct {
		Timestamp     string `json:"timestamp"`
		TraceMetadata any    `json:"trace_metadata"`
		Environment   any    `json:"environment"`
		Results       []struct {
			EventID string `json:"event_id"`
			Status  string `json:"status"`
		} `json:"results"`
		Summary struct {
			TotalEvents      int `json:"total_events"`
			SuccessfulEvents int `json:"successful_events"`
			FailedEvents     int `json:"failed_events"`
		} `json:"summary"`
	}
	if err := json.Unmarshal(body, &cert); err != nil {
		return fmt.Errorf("parse trace replay certificate %s: %w", filepath.Base(certPath), err)
	}
	if _, err := time.Parse(time.RFC3339Nano, cert.Timestamp); err != nil {
		return fmt.Errorf("trace replay certificate %s has invalid timestamp: %w", filepath.Base(certPath), err)
	}

	traceBody, err := os.ReadFile(tracePath)
	if err != nil {
		return fmt.Errorf("read replay trace for certificate binding: %w", err)
	}
	var trace struct {
		Metadata any `json:"metadata"`
		Events   []struct {
			ID string `json:"id"`
		} `json:"events"`
	}
	if err := json.Unmarshal(traceBody, &trace); err != nil {
		return fmt.Errorf("parse replay trace for certificate binding: %w", err)
	}
	if trace.Metadata == nil {
		trace.Metadata = map[string]any{}
	}
	if !reflect.DeepEqual(cert.TraceMetadata, trace.Metadata) {
		return fmt.Errorf("trace replay certificate %s trace_metadata does not match requested trace", filepath.Base(certPath))
	}

	envPath, err := resolveContainedExistingPath(fixturesPath, "env.json")
	if err != nil {
		return fmt.Errorf("resolve replay fixture environment for certificate binding: %w", err)
	}
	envBody, err := os.ReadFile(envPath)
	if err != nil {
		return fmt.Errorf("read replay fixture environment for certificate binding: %w", err)
	}
	var environment any
	if err := json.Unmarshal(envBody, &environment); err != nil {
		return fmt.Errorf("parse replay fixture environment for certificate binding: %w", err)
	}
	if !reflect.DeepEqual(cert.Environment, environment) {
		return fmt.Errorf("trace replay certificate %s environment does not match requested fixtures", filepath.Base(certPath))
	}

	if len(cert.Results) != len(trace.Events) {
		return fmt.Errorf(
			"trace replay certificate %s result count mismatch: expected %d got %d",
			filepath.Base(certPath), len(trace.Events), len(cert.Results),
		)
	}
	successful, failed, skipped := 0, 0, 0
	for i, result := range cert.Results {
		if trace.Events[i].ID == "" {
			return fmt.Errorf("requested replay trace event %d has empty id", i)
		}
		if result.EventID != trace.Events[i].ID {
			return fmt.Errorf(
				"trace replay certificate %s event %d id mismatch: expected %s got %s",
				filepath.Base(certPath), i, trace.Events[i].ID, result.EventID,
			)
		}
		switch result.Status {
		case "success":
			successful++
		case "failed":
			failed++
		case "skipped":
			skipped++
		default:
			return fmt.Errorf("trace replay certificate %s event %s has unsupported status %q", filepath.Base(certPath), result.EventID, result.Status)
		}
	}
	if cert.Summary.TotalEvents != len(cert.Results) ||
		cert.Summary.SuccessfulEvents != successful ||
		cert.Summary.FailedEvents != failed ||
		successful+failed+skipped != len(cert.Results) {
		return fmt.Errorf("trace replay certificate %s summary is inconsistent with results", filepath.Base(certPath))
	}
	if failed != 0 || skipped != 0 || successful != len(cert.Results) {
		return fmt.Errorf("trace replay certificate %s does not show successful replay of every requested event", filepath.Base(certPath))
	}
	return nil
}

func resolveReplayPaths(opts *ReplayOptions, bundle *EvidenceBundle) (tracePath, fixturesPath string, err error) {
	if bundle.ReplayContext != nil {
		if bundle.ReplayContext.KitTracePath != "" {
			tracePath, err = resolveContainedExistingPath(opts.BaseDir, bundle.ReplayContext.KitTracePath)
			if err != nil {
				return "", "", fmt.Errorf("resolve replay trace path: %w", err)
			}
		}
		if bundle.ReplayContext.FixturesPath != "" {
			fixturesPath, err = resolveContainedExistingPath(opts.BaseDir, bundle.ReplayContext.FixturesPath)
			if err != nil {
				return "", "", fmt.Errorf("resolve replay fixtures path: %w", err)
			}
		}
	}
	if opts.FixturesDir != "" {
		fixturesPath, err = resolveContainedExistingPath(opts.BaseDir, opts.FixturesDir)
		if err != nil {
			return "", "", fmt.Errorf("resolve replay fixtures override: %w", err)
		}
	}
	if tracePath == "" {
		for _, ref := range bundle.Artifacts {
			if ref.Role == "execution-trace" {
				tracePath, err = resolveContainedExistingPath(opts.BaseDir, ref.Path)
				if err != nil {
					return "", "", fmt.Errorf("resolve execution trace artifact: %w", err)
				}
				break
			}
		}
	}
	if fixturesPath == "" {
		candidate, candidateErr := resolveContainedExistingPath(opts.BaseDir, "fixtures")
		if candidateErr == nil {
			if st, statErr := os.Stat(candidate); statErr == nil && st.IsDir() {
				fixturesPath = candidate
			}
		}
	}
	if tracePath == "" {
		return "", "", fmt.Errorf("no trace path resolved for execute replay")
	}
	if fixturesPath == "" {
		return "", "", fmt.Errorf("no fixtures path resolved for execute replay")
	}
	if st, statErr := os.Stat(tracePath); statErr != nil {
		return "", "", fmt.Errorf("replay trace path missing: %w", statErr)
	} else if st.IsDir() {
		return "", "", fmt.Errorf("replay trace path is not a file: %s", tracePath)
	}
	if st, statErr := os.Stat(fixturesPath); statErr != nil {
		return "", "", fmt.Errorf("replay fixtures path missing: %w", statErr)
	} else if !st.IsDir() {
		return "", "", fmt.Errorf("replay fixtures path is not a directory: %s", fixturesPath)
	}
	if _, err := resolveContainedExistingPath(fixturesPath, "env.json"); err != nil {
		return "", "", fmt.Errorf("replay fixture env.json invalid: %w", err)
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
