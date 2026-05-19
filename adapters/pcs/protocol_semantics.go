// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"regexp"
	"strings"
)

var patternPlaceholderCommit = regexp.MustCompile(`^(?:a{40}|b{40}|c{40}|d{40}|e{40})$`)

// ValidateHandoffManifestSemantics enforces release-mode handoff rules from pcs-core.
func ValidateHandoffManifestSemantics(h *HandoffManifest) error {
	if h == nil {
		return fmt.Errorf("handoff manifest is nil")
	}
	var errs []string
	scanForbiddenCommits(h, "", &errs)
	if h.Status == HandoffStatusValidated {
		for name, ref := range h.InputArtifacts {
			if strings.TrimSpace(ref.SHA256) == "" {
				errs = append(errs, fmt.Sprintf("input_artifacts.%s: sha256 required when handoff status is Validated", name))
			}
		}
	}
	if len(errs) > 0 {
		return fmt.Errorf("%s", strings.Join(errs, "; "))
	}
	return nil
}

// ValidateReleaseManifestSemantics enforces release-mode manifest rules from pcs-core.
func ValidateReleaseManifestSemantics(m *ReleaseManifest) error {
	if m == nil {
		return fmt.Errorf("release manifest is nil")
	}
	var errs []string
	if !isScientificComputationConformanceManifest(m) {
		scanForbiddenCommits(m.ProducerRepos, "producer_repos", &errs)
		for name, entry := range m.Artifacts {
			scanForbiddenCommits(entry, "artifacts."+name, &errs)
		}
	}
	if m.ReleaseStatus == "Validated" {
		for name, entry := range m.Artifacts {
			if strings.TrimSpace(entry.SHA256) == "" {
				errs = append(errs, fmt.Sprintf("artifacts.%s: sha256 required when release_status is Validated", name))
			}
		}
	}
	if len(errs) > 0 {
		return fmt.Errorf("%s", strings.Join(errs, "; "))
	}
	return nil
}

// ValidateReleaseChainValidationResultSemantics enforces RCVR consistency rules.
func ValidateReleaseChainValidationResultSemantics(r *ReleaseChainValidationResult) error {
	if r == nil {
		return fmt.Errorf("release chain validation result is nil")
	}
	var errs []string
	scanForbiddenCommits(r, "", &errs)
	failed := 0
	for _, c := range r.Checks {
		if c.Status == "failed" {
			failed++
		}
	}
	hasFailures := failed > 0 || len(r.FailureCodes) > 0
	if r.Status == StatusProofChecked && hasFailures {
		errs = append(errs, "ReleaseChainValidationResult.v0 cannot use status ProofChecked with failed checks or failure_codes")
	}
	if r.Status == StatusRejected && !hasFailures {
		errs = append(errs, "ReleaseChainValidationResult.v0 with status Rejected requires failed checks or failure_codes")
	}
	if len(errs) > 0 {
		return fmt.Errorf("%s", strings.Join(errs, "; "))
	}
	return nil
}

func scanForbiddenCommits(obj any, path string, errs *[]string) {
	switch t := obj.(type) {
	case map[string]any:
		if local, ok := t["local_dev"].(bool); ok && local {
			*errs = append(*errs, fmt.Sprintf("%s: local_dev=true forbidden in release mode", orRoot(path)))
		}
		for _, field := range []string{"source_commit", "commit"} {
			if commit, ok := t[field].(string); ok {
				if reason := forbiddenCommit(commit); reason != "" {
					*errs = append(*errs, fmt.Sprintf("%s: %s %s: %s", orRoot(path), field, reason, commit))
				}
			}
		}
		for k, v := range t {
			child := path
			if child != "" {
				child += "."
			}
			child += k
			scanForbiddenCommits(v, child, errs)
		}
	case map[string]ProducerRepoPin:
		for k, pin := range t {
			scanForbiddenCommits(pin, path+"."+k, errs)
		}
	case map[string]ManifestArtifactEntry:
		for k, entry := range t {
			scanForbiddenCommits(entry, path+"."+k, errs)
		}
	case map[string]HandoffArtifactRef:
		for k, ref := range t {
			scanForbiddenCommits(ref, path+"."+k, errs)
		}
	case ProducerRepoPin:
		scanForbiddenCommits(map[string]any{
			"repo":          t.Repo,
			"commit":        t.Commit,
			"local_dev":     t.LocalDev,
			"source_commit": t.Commit,
		}, path, errs)
	case ManifestArtifactEntry:
		scanForbiddenCommits(map[string]any{
			"source_commit": t.SourceCommit,
			"local_dev":     t.LocalDev,
		}, path, errs)
	case HandoffManifest:
		scanForbiddenCommits(map[string]any{
			"source_commit": t.SourceCommit,
		}, path, errs)
	case ReleaseManifest:
		scanForbiddenCommits(t.ProducerRepos, "producer_repos", errs)
		for name, entry := range t.Artifacts {
			scanForbiddenCommits(entry, "artifacts."+name, errs)
		}
	case ReleaseChainValidationResult:
		scanForbiddenCommits(map[string]any{
			"source_commit": t.SourceCommit,
		}, path, errs)
	case []any:
		for i, item := range t {
			scanForbiddenCommits(item, fmt.Sprintf("%s[%d]", path, i), errs)
		}
	}
}

func orRoot(path string) string {
	if path == "" {
		return "root"
	}
	return path
}

func forbiddenCommit(commit string) string {
	stripped := strings.TrimSpace(commit)
	if stripped == ZeroSourceCommitPlaceholder {
		return "zero source_commit"
	}
	if patternPlaceholderCommit.MatchString(stripped) {
		return "pattern placeholder source_commit"
	}
	return ""
}

// isScientificComputationConformanceManifest is true for pcs-core computation-release
// examples that intentionally use pattern placeholder producer commits (a–e runs).
func isScientificComputationConformanceManifest(m *ReleaseManifest) bool {
	if m == nil {
		return false
	}
	profile := strings.TrimSpace(m.ValidationProfile)
	return strings.HasPrefix(profile, "scientific_computation.")
}
