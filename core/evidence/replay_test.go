// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestReplayValidFixture(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid", "basic-evidence-bundle.json")
	out := filepath.Join(t.TempDir(), "replay-report.json")
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		OutPath:    out,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
	})
	if err != nil {
		t.Fatalf("replay: %v (%v)", err, report.Errors)
	}
	if !report.TraceFound {
		t.Fatal("expected execution trace in fixture bundle")
	}
}

func TestReplayTamperedDigestFails(t *testing.T) {
	root := repoRoot(t)
	bad := filepath.Join(root, "specs", "evidence", "v0.1", "examples", "invalid", "bad-bundle-digest.json")
	_, err := ReplayBundle(ReplayOptions{
		BundlePath: bad,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bad),
	})
	if err == nil {
		t.Fatal("expected replay failure for tampered bundle")
	}
}

const validTraceReplayCert = `{
  "$schema": "https://provability-fabric.org/schemas/evidence/v0.2/trace-replay-cert.schema.json",
  "cert_type": "trace_replay",
  "version": "1.0.0",
  "timestamp": "2026-07-23T14:38:09Z",
  "replay_id": "fedac781428bba62",
  "trace_metadata": {
    "version": "1.0.0",
    "created_at": "2024-01-01T00:00:00Z",
    "system_info": {
      "name": "simple_call_test",
      "version": "1.0.0"
    }
  },
  "environment": {
    "locale": "en_US.UTF-8",
    "timezone": "UTC",
    "seed": 42,
    "versions": {
      "python": "3.11.0",
      "system_lib": "1.0.0"
    }
  },
  "results": [
    {
      "event_id": "event_001",
      "status": "success"
    }
  ],
  "summary": {
    "total_events": 1,
    "successful_events": 1,
    "failed_events": 0
  },
  "signature": {
    "algorithm": "sha256",
    "hash": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
  }
}`
const invalidTraceReplayCert = `{"cert_type":"trace_replay"}`

type fixtureKITRunner struct {
	firstBody     string
	secondBody    string
	omitFirst     bool
	omitSecond    bool
	firstCode     int
	secondCode    int
	secondErr     error
	runCount      int
	compareCalled bool
}

func (r *fixtureKITRunner) Run(_, _, certOut string) (int, error) {
	r.runCount++
	if r.runCount == 2 && r.secondErr != nil {
		return 0, r.secondErr
	}
	code := 0
	if r.runCount == 1 {
		code = r.firstCode
	} else if r.runCount == 2 {
		code = r.secondCode
	}
	if code != 0 {
		return code, nil
	}
	omit := (r.runCount == 1 && r.omitFirst) || (r.runCount == 2 && r.omitSecond)
	if omit {
		return 0, nil
	}
	body := validTraceReplayCert
	if r.runCount == 1 && r.firstBody != "" {
		body = r.firstBody
	}
	if r.runCount == 2 && r.secondBody != "" {
		body = r.secondBody
	}
	if err := os.MkdirAll(filepath.Dir(certOut), 0755); err != nil {
		return 1, err
	}
	if err := os.WriteFile(certOut, []byte(body), 0644); err != nil {
		return 1, err
	}
	return 0, nil
}

func (r *fixtureKITRunner) CompareLowView(_ []string, _ float64) (int, error) {
	r.compareCalled = true
	return 0, nil
}

func TestReplayExecuteValidatesGeneratedCertificates(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err != nil {
		t.Fatalf("execute replay: %v (%v)", err, report.Errors)
	}
	if report.ExecuteStatus != "pass" {
		t.Fatalf("expected execute_status pass, got %q", report.ExecuteStatus)
	}
	if report.ReplayCertValidation != "pass" {
		t.Fatalf("expected replay certificate validation pass, got %q", report.ReplayCertValidation)
	}
	if report.ReplayCertSchema != "specs/evidence/v0.2/schemas/trace-replay-cert.schema.json" {
		t.Fatalf("unexpected replay certificate schema %q", report.ReplayCertSchema)
	}
	if len(report.ReplayArtifacts) != 2 {
		t.Fatalf("expected two replay certificate artifacts, got %v", report.ReplayArtifacts)
	}
	if report.KitExitCode == nil || *report.KitExitCode != 0 || report.KitSecondExitCode == nil || *report.KitSecondExitCode != 0 {
		t.Fatalf("expected both KIT runs to record exit code 0, first=%v second=%v", report.KitExitCode, report.KitSecondExitCode)
	}
	if !runner.compareCalled {
		t.Fatal("expected low-view comparison after both certificates validated")
	}
}

func TestReplayExecuteRejectsInvalidTimestamp(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	invalidTimestamp := strings.Replace(validTraceReplayCert, "2026-07-23T14:38:09Z", "not-a-timestamp", 1)
	runner := &fixtureKITRunner{firstBody: invalidTimestamp}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected invalid replay timestamp to fail closed")
	}
	if report.ReplayCertValidation != "fail" || report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("unexpected invalid-timestamp report: %+v", report)
	}
}

func TestReplayExecuteRejectsInvalidFirstGeneratedCertificate(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{firstBody: invalidTraceReplayCert}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected invalid first generated replay certificate to fail closed")
	}
	if report.ReplayCertValidation != "fail" {
		t.Fatalf("expected replay certificate validation fail, got %q", report.ReplayCertValidation)
	}
	if report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("expected replay and execute status fail, got status=%q execute=%q", report.Status, report.ExecuteStatus)
	}
	if len(report.ReplayArtifacts) != 0 {
		t.Fatalf("invalid certificate must not be reported as a validated replay artifact: %v", report.ReplayArtifacts)
	}
	if runner.runCount != 1 || runner.compareCalled {
		t.Fatalf("expected immediate failure before second run/compare, runs=%d compare=%v", runner.runCount, runner.compareCalled)
	}
}

func TestReplayExecuteRejectsInvalidSecondGeneratedCertificateBeforeLowView(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{secondBody: invalidTraceReplayCert}
	reportPath := filepath.Join(t.TempDir(), "replay-report.json")
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		OutPath:    reportPath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected invalid second generated replay certificate to fail closed")
	}
	if report.ReplayCertValidation != "fail" || report.LowViewResult != "fail" || report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("unexpected failure report: %+v", report)
	}
	if len(report.ReplayArtifacts) != 1 || report.ReplayArtifacts[0] != "replay.cert.json" {
		t.Fatalf("only the first validated certificate may be reported: %v", report.ReplayArtifacts)
	}
	if runner.runCount != 2 || runner.compareCalled {
		t.Fatalf("low-view compare must not run after invalid second cert, runs=%d compare=%v", runner.runCount, runner.compareCalled)
	}
	raw, readErr := os.ReadFile(reportPath)
	if readErr != nil {
		t.Fatalf("expected failure replay report to be persisted: %v", readErr)
	}
	var persisted ReplayReport
	if err := json.Unmarshal(raw, &persisted); err != nil {
		t.Fatalf("parse persisted replay report: %v", err)
	}
	if persisted.ExecuteStatus != "fail" || persisted.Status != "fail" || persisted.ReplayCertValidation != "fail" {
		t.Fatalf("persisted report must record execute_status fail, got %+v", persisted)
	}
}

func TestReplayExecuteRejectsMissingFirstCertificateOnZeroExit(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{omitFirst: true}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected missing first certificate to fail closed despite zero runner exit")
	}
	if report.ReplayCertValidation != "fail" || report.ExecuteStatus != "fail" || report.Status != "fail" {
		t.Fatalf("unexpected missing-cert report: %+v", report)
	}
	if len(report.ReplayArtifacts) != 0 || runner.runCount != 1 || runner.compareCalled {
		t.Fatalf("missing cert must stop replay before artifact/compare, artifacts=%v runs=%d compare=%v", report.ReplayArtifacts, runner.runCount, runner.compareCalled)
	}
}

func TestReplayExecuteRejectsMissingSecondCertificateBeforeLowView(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{omitSecond: true}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected missing second certificate to fail closed despite zero runner exit")
	}
	if report.ReplayCertValidation != "fail" || report.LowViewResult != "fail" || report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("unexpected missing-second-cert report: %+v", report)
	}
	if len(report.ReplayArtifacts) != 1 || report.ReplayArtifacts[0] != "replay.cert.json" {
		t.Fatalf("only first validated cert may be reported: %v", report.ReplayArtifacts)
	}
	if runner.runCount != 2 || runner.compareCalled {
		t.Fatalf("low-view compare must not run without second cert, runs=%d compare=%v", runner.runCount, runner.compareCalled)
	}
}

func TestReplayExecuteSecondRunnerNonzeroDoesNotReportCertificateValidationPass(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{secondCode: 7}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected second runner nonzero exit to fail replay")
	}
	if report.ReplayCertValidation != "fail" || report.LowViewResult != "fail" || report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("second-run failure must not retain a certificate-validation pass: %+v", report)
	}
	if len(report.ReplayArtifacts) != 1 || report.ReplayArtifacts[0] != "replay.cert.json" {
		t.Fatalf("only first validated cert may be reported: %v", report.ReplayArtifacts)
	}
	if report.KitSecondExitCode == nil || *report.KitSecondExitCode != 7 {
		t.Fatalf("expected second KIT exit code 7 to be retained, got %v", report.KitSecondExitCode)
	}
	if runner.runCount != 2 || runner.compareCalled {
		t.Fatalf("low-view compare must not run after second runner failure, runs=%d compare=%v", runner.runCount, runner.compareCalled)
	}
}

func TestReplayExecuteSecondRunnerErrorDoesNotReportCertificateValidationPass(t *testing.T) {
	root := repoRoot(t)
	bundlePath := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "deep-replay-bundle.json")
	runner := &fixtureKITRunner{secondErr: fmt.Errorf("second runner failed")}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: bundlePath,
		RepoRoot:   root,
		BaseDir:    filepath.Dir(bundlePath),
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     runner,
	})
	if err == nil {
		t.Fatal("expected second runner error to fail replay")
	}
	if report.ReplayCertValidation != "fail" || report.LowViewResult != "fail" || report.Status != "fail" || report.ExecuteStatus != "fail" {
		t.Fatalf("second-run error must not retain a certificate-validation pass: %+v", report)
	}
	if len(report.ReplayArtifacts) != 1 || report.ReplayArtifacts[0] != "replay.cert.json" {
		t.Fatalf("only first validated cert may be reported: %v", report.ReplayArtifacts)
	}
	if runner.runCount != 2 || runner.compareCalled {
		t.Fatalf("low-view compare must not run after second runner error, runs=%d compare=%v", runner.runCount, runner.compareCalled)
	}
}

func writeReplayCertFixture(t *testing.T, body string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), "replay.cert.json")
	if err := os.WriteFile(path, []byte(body), 0644); err != nil {
		t.Fatalf("write replay certificate fixture: %v", err)
	}
	return path
}

func deepReplayInputPaths(t *testing.T) (root, tracePath, fixturesPath string) {
	t.Helper()
	root = repoRoot(t)
	base := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid")
	tracePath = filepath.Join(base, "kit", "trace.json")
	fixturesPath = filepath.Join(base, "kit", "fixtures")
	return root, tracePath, fixturesPath
}

func TestTraceReplayCertificateBindsToRequestedInputs(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	certPath := writeReplayCertFixture(t, validTraceReplayCert)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err != nil {
		t.Fatalf("expected bound replay certificate to validate: %v", err)
	}
}

func TestTraceReplayCertificateRejectsTraceMetadataMismatch(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"name": "simple_call_test"`, `"name": "different_trace"`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "trace_metadata") {
		t.Fatalf("expected trace metadata mismatch, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsEnvironmentMismatch(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"locale": "en_US.UTF-8"`, `"locale": "fr_FR.UTF-8"`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "environment") {
		t.Fatalf("expected environment mismatch, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsEventIDMismatch(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"event_id": "event_001"`, `"event_id": "event_999"`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "id mismatch") {
		t.Fatalf("expected event id mismatch, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsNonSuccessfulEvent(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"status": "success"`, `"status": "skipped"`, 1)
	body = strings.Replace(body, `"successful_events": 1`, `"successful_events": 0`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "successful replay of every requested event") {
		t.Fatalf("expected non-success replay rejection, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsSummaryMismatch(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"successful_events": 1`, `"successful_events": 0`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "summary is inconsistent") {
		t.Fatalf("expected summary mismatch, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsResultCountMismatch(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"results": [
    {
      "event_id": "event_001",
      "status": "success"
    }
  ]`, `"results": [
    {
      "event_id": "event_001",
      "status": "success"
    },
    {
      "event_id": "event_002",
      "status": "success"
    }
  ]`, 1)
	body = strings.Replace(body, `"total_events": 1`, `"total_events": 2`, 1)
	body = strings.Replace(body, `"successful_events": 1`, `"successful_events": 2`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "result count mismatch") {
		t.Fatalf("expected result count mismatch, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsEmptyRequestedTrace(t *testing.T) {
	root := repoRoot(t)
	tmp := t.TempDir()
	tracePath := filepath.Join(tmp, "trace.json")
	if err := os.WriteFile(tracePath, []byte(`{"metadata":{"version":"1.0.0"},"events":[]}`), 0644); err != nil {
		t.Fatal(err)
	}
	fixturesPath := filepath.Join(tmp, "fixtures")
	if err := os.MkdirAll(fixturesPath, 0755); err != nil {
		t.Fatal(err)
	}
	envSrc := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid", "kit", "fixtures", "env.json")
	envBody, err := os.ReadFile(envSrc)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(fixturesPath, "env.json"), envBody, 0644); err != nil {
		t.Fatal(err)
	}
	certPath := writeReplayCertFixture(t, validTraceReplayCert)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "no events") {
		t.Fatalf("expected empty requested trace to fail, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsAdditionalProperties(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(validTraceReplayCert, `"cert_type": "trace_replay",`, `"cert_type": "trace_replay",
  "unexpected_field": true,`, 1)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil || !strings.Contains(err.Error(), "schema validation") {
		t.Fatalf("expected additional property rejection, got %v", err)
	}
}

func TestTraceReplayCertificateRejectsCertV1SchemaAuthority(t *testing.T) {
	root, tracePath, fixturesPath := deepReplayInputPaths(t)
	body := strings.Replace(
		validTraceReplayCert,
		"https://provability-fabric.org/schemas/evidence/v0.2/trace-replay-cert.schema.json",
		"https://raw.githubusercontent.com/verifiable-ai-ci/CERT-V1/v1.0.0/schema/cert-v1.json",
		1,
	)
	certPath := writeReplayCertFixture(t, body)
	if err := validateTraceReplayCert(root, certPath, tracePath, fixturesPath); err == nil {
		t.Fatal("expected CERT-V1 schema authority to fail")
	}
}

func TestReplayExecuteRejectsTamperedKitTraceBytes(t *testing.T) {
	root := repoRoot(t)
	src := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid")
	dst := t.TempDir()
	copyDir(t, src, dst)
	trace := filepath.Join(dst, "kit", "trace.json")
	data, err := os.ReadFile(trace)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(trace, append(data, []byte("\n")...), 0644); err != nil {
		t.Fatal(err)
	}
	_, err = ReplayBundle(ReplayOptions{
		BundlePath: filepath.Join(dst, "deep-replay-bundle.json"),
		RepoRoot:   root,
		BaseDir:    dst,
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     &fixtureKITRunner{},
	})
	if err == nil {
		t.Fatal("expected swapped kit trace bytes without digest update to fail")
	}
	if !strings.Contains(err.Error(), "digest") {
		t.Fatalf("expected digest-binding failure, got %v", err)
	}
}

func TestReplayExecuteRejectsEmptyKitTrace(t *testing.T) {
	root := repoRoot(t)
	src := filepath.Join(root, "specs", "evidence", "v0.2", "examples", "valid")
	dst := t.TempDir()
	copyDir(t, src, dst)
	emptyTrace := []byte(`{
  "metadata": {
    "version": "1.0.0",
    "created_at": "2024-01-01T00:00:00Z",
    "system_info": {"name": "simple_call_test", "version": "1.0.0"}
  },
  "events": []
}
`)
	if err := os.WriteFile(filepath.Join(dst, "kit", "trace.json"), emptyTrace, 0644); err != nil {
		t.Fatal(err)
	}
	if _, err := Pack(PackOptions{
		ManifestPath: filepath.Join(dst, "manifest.json"),
		OutPath:      filepath.Join(dst, "deep-replay-bundle.json"),
		BaseDir:      dst,
	}); err != nil {
		t.Fatalf("pack empty-trace bundle: %v", err)
	}
	report, err := ReplayBundle(ReplayOptions{
		BundlePath: filepath.Join(dst, "deep-replay-bundle.json"),
		RepoRoot:   root,
		BaseDir:    dst,
		Execute:    true,
		OutDir:     t.TempDir(),
		Runner:     &fixtureKITRunner{},
	})
	if err == nil {
		t.Fatal("expected empty kit trace execute to fail closed")
	}
	if report.ExecuteStatus != "fail" || report.Status != "fail" {
		t.Fatalf("expected execute_status fail for empty trace, got %+v", report)
	}
	if !strings.Contains(err.Error(), "no events") {
		t.Fatalf("expected empty-events failure, got %v", err)
	}
}

func copyDir(t *testing.T, src, dst string) {
	t.Helper()
	err := filepath.Walk(src, func(path string, info os.FileInfo, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		rel, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}
		target := filepath.Join(dst, rel)
		if info.IsDir() {
			return os.MkdirAll(target, 0755)
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		return os.WriteFile(target, data, 0644)
	})
	if err != nil {
		t.Fatalf("copy dir: %v", err)
	}
}

func TestResolveReplayPathsReturnsContainedResolvedInputs(t *testing.T) {
	base := t.TempDir()
	traceDir := filepath.Join(base, "kit")
	fixtures := filepath.Join(traceDir, "fixtures")
	if err := os.MkdirAll(fixtures, 0755); err != nil {
		t.Fatal(err)
	}
	trace := filepath.Join(traceDir, "trace.json")
	if err := os.WriteFile(trace, []byte(`{"metadata":{},"events":[]}`), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(fixtures, "env.json"), []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	bundle := EvidenceBundle{ReplayContext: &ReplayContext{KitTracePath: "kit/trace.json", FixturesPath: "kit/fixtures"}}
	tracePath, fixturesPath, err := resolveReplayPaths(&ReplayOptions{BaseDir: base}, &bundle)
	if err != nil {
		t.Fatalf("resolve replay paths: %v", err)
	}
	if !filepath.IsAbs(tracePath) || !filepath.IsAbs(fixturesPath) {
		t.Fatalf("expected absolute resolved paths")
	}
}

func TestResolveReplayPathsRejectsTraversal(t *testing.T) {
	root := t.TempDir()
	base := filepath.Join(root, "base")
	outside := filepath.Join(root, "outside")
	if err := os.MkdirAll(filepath.Join(base, "fixtures"), 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(outside, 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(base, "fixtures", "env.json"), []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(outside, "trace.json"), []byte(`{"metadata":{},"events":[]}`), 0644); err != nil {
		t.Fatal(err)
	}
	bundle := EvidenceBundle{ReplayContext: &ReplayContext{KitTracePath: "../outside/trace.json", FixturesPath: "fixtures"}}
	if _, _, err := resolveReplayPaths(&ReplayOptions{BaseDir: base}, &bundle); err == nil {
		t.Fatal("expected traversal outside replay base to fail")
	}
}

func TestResolveReplayPathsRejectsEscapingFixtureEnvSymlink(t *testing.T) {
	root := t.TempDir()
	base := filepath.Join(root, "base")
	fixtures := filepath.Join(base, "fixtures")
	if err := os.MkdirAll(fixtures, 0755); err != nil {
		t.Fatal(err)
	}
	trace := filepath.Join(base, "trace.json")
	if err := os.WriteFile(trace, []byte(`{"metadata":{},"events":[]}`), 0644); err != nil {
		t.Fatal(err)
	}
	outsideEnv := filepath.Join(root, "outside-env.json")
	if err := os.WriteFile(outsideEnv, []byte(`{}`), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outsideEnv, filepath.Join(fixtures, "env.json")); err != nil {
		t.Skipf("symlink unavailable: %v", err)
	}
	bundle := EvidenceBundle{ReplayContext: &ReplayContext{KitTracePath: "trace.json", FixturesPath: "fixtures"}}
	if _, _, err := resolveReplayPaths(&ReplayOptions{BaseDir: base}, &bundle); err == nil {
		t.Fatal("expected fixture env symlink escape to fail")
	}
}
