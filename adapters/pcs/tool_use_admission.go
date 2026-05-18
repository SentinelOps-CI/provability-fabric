// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

// ToolUseScienceClaimBundle is the expected envelope for agent_tool_use_safety (skeleton).
type ToolUseScienceClaimBundle struct {
	BundleID           string                `json:"bundle_id"`
	SchemaVersion      string                `json:"schema_version"`
	ToolUseTrace       *ToolUseTraceV0       `json:"tool_use_trace"`
	ToolUseCertificate *ToolUseCertificateV0 `json:"tool_use_certificate"`
	Producer           string                `json:"producer,omitempty"`
	SourceCommit       string                `json:"source_commit,omitempty"`
}

// ToolUseTraceV0 is a minimal tool-use trace artifact (skeleton).
type ToolUseTraceV0 struct {
	SchemaVersion  string `json:"schema_version"`
	TraceID        string `json:"trace_id"`
	ToolTraceHash  string `json:"tool_trace_hash"`
	Producer       string `json:"producer,omitempty"`
	SourceCommit   string `json:"source_commit,omitempty"`
}

// ToolUseCertificateV0 is a minimal tool-use certificate artifact (skeleton).
type ToolUseCertificateV0 struct {
	SchemaVersion       string   `json:"schema_version"`
	CertificateID       string   `json:"certificate_id"`
	Status              string   `json:"status"`
	ToolTraceHash       string   `json:"tool_trace_hash"`
	AuthorizedToolCalls []string `json:"authorized_tool_calls,omitempty"`
	Violations          []string `json:"violations,omitempty"`
	Producer            string   `json:"producer,omitempty"`
}

func loadToolUseBundle(path string) (*ToolUseScienceClaimBundle, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, err
	}
	var bundle ToolUseScienceClaimBundle
	if err := json.Unmarshal(data, &bundle); err != nil {
		return nil, fmt.Errorf("parse tool-use bundle: %w", err)
	}
	return &bundle, nil
}

func enforceAgentToolUseSafetyProfile(profile *AdmissionProfile, bundlePath string) error {
	if strings.TrimSpace(bundlePath) == "" {
		return fmt.Errorf("%s: tool-use profile requires a bundle path", FailureCodeReleaseModeBundleRequired)
	}
	bundle, err := loadToolUseBundle(bundlePath)
	if err != nil {
		// ScienceClaimBundle-shaped input is the common mistake before tool-use artifacts exist.
		if scb, loadErr := LoadScienceClaimBundle(bundlePath); loadErr == nil && scb != nil {
			return fmt.Errorf("%s: missing ToolUseTrace.v0 (bundle %q is %s, profile requires %s)",
				FailureCodeMissingToolUseTrace, scb.BundleID, "ScienceClaimBundle.v0", profile.AcceptedBundleArtifact)
		}
		return fmt.Errorf("%s: %w", FailureCodeMissingToolUseTrace, err)
	}
	if bundle.ToolUseTrace == nil {
		return fmt.Errorf("%s: missing ToolUseTrace.v0 in bundle %q", FailureCodeMissingToolUseTrace, bundle.BundleID)
	}
	if strings.TrimSpace(bundle.ToolUseTrace.ToolTraceHash) == "" {
		return fmt.Errorf("%s: ToolUseTrace.v0.tool_trace_hash is empty", FailureCodeMissingToolUseTrace)
	}
	if bundle.ToolUseCertificate == nil {
		return fmt.Errorf("%s: missing ToolUseCertificate.v0 in bundle %q", FailureCodeMissingToolUseCertificate, bundle.BundleID)
	}
	cert := bundle.ToolUseCertificate
	if cert.Status == StatusRejected {
		return fmt.Errorf("%s: ToolUseCertificate.v0 status is Rejected", FailureCodeToolUseCertificateRejected)
	}
	if strings.TrimSpace(cert.ToolTraceHash) == "" {
		return fmt.Errorf("%s: ToolUseCertificate.v0.tool_trace_hash is empty", FailureCodeMissingToolUseCertificate)
	}
	if cert.ToolTraceHash != bundle.ToolUseTrace.ToolTraceHash {
		return fmt.Errorf("%s: certificate tool_trace_hash %s != trace %s",
			FailureCodeToolTraceHashMismatch, cert.ToolTraceHash, bundle.ToolUseTrace.ToolTraceHash)
	}
	if len(cert.Violations) > 0 {
		return fmt.Errorf("%s: certificate reports violations: %v", FailureCodeUnauthorizedToolCallViolation, cert.Violations)
	}
	for _, call := range cert.AuthorizedToolCalls {
		if strings.HasPrefix(strings.ToLower(call), "deny:") || strings.Contains(strings.ToLower(call), "unauthorized") {
			return fmt.Errorf("%s: unauthorized tool call %q", FailureCodeUnauthorizedToolCallViolation, call)
		}
	}
	return nil
}
