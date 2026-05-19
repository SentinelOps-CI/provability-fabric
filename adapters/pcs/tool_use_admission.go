// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// ToolUseTraceV0 is a minimal tool-use trace artifact (skeleton).
type ToolUseTraceV0 struct {
	SchemaVersion string `json:"schema_version"`
	TraceID       string `json:"trace_id"`
	ToolTraceHash string `json:"tool_trace_hash"`
	Producer      string `json:"producer,omitempty"`
	SourceCommit  string `json:"source_commit,omitempty"`
}

// ToolUseCertificateV0 is a minimal tool-use certificate artifact (skeleton).
type ToolUseCertificateV0 struct {
	SchemaVersion       string   `json:"schema_version"`
	CertificateID       string   `json:"certificate_id"`
	Status              string   `json:"status"`
	ToolTraceHash       string   `json:"tool_trace_hash"`
	PolicyHash          string   `json:"policy_hash,omitempty"`
	AuthorizedToolCalls []string `json:"authorized_tool_calls,omitempty"`
	Violations          []string `json:"violations,omitempty"`
	Producer            string   `json:"producer,omitempty"`
}

const workflowAgentToolUseSafety = "agent_tool_use.safety_v0"
const workflowLabtrustQCRelease = "labtrust.qc_release_v0"

// InferBundleWorkflowID returns the PCS workflow id implied by bundle contents.
func InferBundleWorkflowID(bundle *ScienceClaimBundle) string {
	if bundle == nil {
		return ""
	}
	if w := strings.TrimSpace(bundle.WorkflowID); w != "" {
		return w
	}
	if bundle.ToolUseTrace != nil || bundle.ToolUseCertificate != nil {
		return workflowAgentToolUseSafety
	}
	if inferComputationWorkflow(bundle) {
		return workflowScientificComputationRepro
	}
	if bundle.VerificationPolicy != nil {
		if w := strings.TrimSpace(bundle.VerificationPolicy.PolicyID); strings.HasPrefix(w, "scientific_computation") {
			return workflowScientificComputationRepro
		}
	}
	if len(bundle.Certificates) > 0 {
		return workflowLabtrustQCRelease
	}
	return ""
}

func enforceAgentToolUseSafetyProfile(profile *AdmissionProfile, bundle *ScienceClaimBundle, handoff *LoadedHandoff, releaseMode bool) error {
	if bundle == nil {
		return fmt.Errorf("%s: profile %q requires a science claim bundle", FailureCodeReleaseModeBundleRequired, profile.ProfileID)
	}
	if profile.AcceptedBundleArtifact != "" && profile.AcceptedBundleArtifact != "ScienceClaimBundle.v0" {
		return fmt.Errorf("%s: profile %q accepts %s only", FailureCodeAdmissionProfileWorkflowMismatch, profile.ProfileID, profile.AcceptedBundleArtifact)
	}
	if inferComputationWorkflow(bundle) {
		return fmt.Errorf("%s: bundle %q is scientific computation workflow %q, profile %q expects %q",
			FailureCodeAdmissionProfileWorkflowMismatch, bundle.BundleID, InferBundleWorkflowID(bundle), profile.ProfileID, profile.WorkflowID)
	}
	if err := validateAdmissionProfileWorkflow(profile, bundle); err != nil {
		return err
	}
	if releaseMode {
		if err := enforceProfileHandoff(profile, handoff); err != nil {
			return err
		}
	}
	for _, rt := range profile.RequiredRuntimeArtifacts {
		switch rt {
		case "ToolUseTrace.v0":
			if bundle.ToolUseTrace == nil {
				return requiredArtifactMissing(profile, rt)
			}
			if strings.TrimSpace(bundle.ToolUseTrace.ToolTraceHash) == "" {
				return fmt.Errorf("%s: ToolUseTrace.v0.tool_trace_hash is empty", FailureCodeMissingToolUseTrace)
			}
		case "RuntimeReceipt.v0":
			if bundle.PrimaryRuntimeReceipt() == nil {
				return requiredArtifactMissing(profile, rt)
			}
		default:
			return fmt.Errorf("%s: profile %q runtime artifact %q is not supported yet", FailureCodeReleaseModeProfileRejected, profile.ProfileID, rt)
		}
	}
	for _, certType := range profile.RequiredCertificateArtifacts {
		if certType != "ToolUseCertificate.v0" {
			continue
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
		if bundle.ToolUseTrace != nil && cert.ToolTraceHash != bundle.ToolUseTrace.ToolTraceHash {
			return fmt.Errorf("%s: certificate tool_trace_hash %s != trace %s",
				FailureCodeToolTraceHashMismatch, cert.ToolTraceHash, bundle.ToolUseTrace.ToolTraceHash)
		}
		if err := validateToolUsePolicyHash(bundle); err != nil {
			return err
		}
		if len(cert.Violations) > 0 {
			return fmt.Errorf("%s: certificate reports violations: %v", FailureCodeUnauthorizedToolCallViolation, cert.Violations)
		}
		for _, call := range cert.AuthorizedToolCalls {
			if strings.HasPrefix(strings.ToLower(call), "deny:") || strings.Contains(strings.ToLower(call), "unauthorized") {
				return fmt.Errorf("%s: unauthorized tool call %q", FailureCodeUnauthorizedToolCallViolation, call)
			}
		}
	}
	return nil
}

func validateToolUsePolicyHash(bundle *ScienceClaimBundle) error {
	cert := bundle.ToolUseCertificate
	if cert == nil || strings.TrimSpace(cert.PolicyHash) == "" {
		return nil
	}
	receipt := bundle.PrimaryRuntimeReceipt()
	if receipt == nil || strings.TrimSpace(receipt.PolicyHash) == "" {
		return nil
	}
	if cert.PolicyHash != receipt.PolicyHash {
		return fmt.Errorf("%s: certificate policy_hash %s != runtime receipt %s",
			FailureCodePolicyHashMismatch, cert.PolicyHash, receipt.PolicyHash)
	}
	return nil
}

func requiredArtifactMissing(profile *AdmissionProfile, artifact string) error {
	return fmt.Errorf("%s: profile %q requires %s",
		FailureCodeAdmissionProfileRequiredArtifactMissing, profile.ProfileID, artifact)
}

func validateAdmissionProfileWorkflow(profile *AdmissionProfile, bundle *ScienceClaimBundle) error {
	if profile == nil || bundle == nil {
		return nil
	}
	expected := strings.TrimSpace(profile.WorkflowID)
	if expected == "" {
		return nil
	}
	actual := InferBundleWorkflowID(bundle)
	if actual == "" {
		return nil
	}
	if actual != expected {
		return fmt.Errorf("%s: bundle workflow %q does not match profile %q (expects workflow %q)",
			FailureCodeAdmissionProfileWorkflowMismatch, actual, profile.ProfileID, expected)
	}
	return nil
}
