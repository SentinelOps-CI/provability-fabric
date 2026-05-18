// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// FailureExplanation is one actionable failure line for operators.
type FailureExplanation struct {
	CheckID              string `json:"check_id"`
	ArtifactPath         string `json:"artifact_path,omitempty"`
	Expected             string `json:"expected,omitempty"`
	Actual               string `json:"actual,omitempty"`
	ResponsibleComponent string `json:"responsible_component,omitempty"`
	RepairHint           string `json:"repair_hint"`
	RegenerateCmd        string `json:"regenerate_command,omitempty"`
}

// ExplainVerificationFailures returns repair hints for failed verification checks.
func ExplainVerificationFailures(result VerificationResult) []FailureExplanation {
	var out []FailureExplanation
	for _, c := range FailedChecks(result) {
		out = append(out, explainVerificationCheck(c)...)
	}
	return out
}

// ExplainReleaseChainFailures returns repair hints for failed release-chain checks.
func ExplainReleaseChainFailures(result ReleaseChainValidationResult) []FailureExplanation {
	var out []FailureExplanation
	for _, c := range result.Checks {
		if c.Status != "failed" {
			continue
		}
		out = append(out, explainReleaseChainCheck(c)...)
	}
	return out
}

func explainVerificationCheck(c VerificationCheck) []FailureExplanation {
	code, _ := c.Details["reason_code"].(string)
	switch c.CheckID {
	case "trace_hash_alignment":
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: ComponentLabTrustGym,
			RepairHint:           "Re-export trace and runtime receipt from LabTrust, re-run CertifyEdge, and re-attach the certificate.",
			RegenerateCmd:        "labtrust export-trace ... && certifyedge emit-pcs-certificate --handoff handoff_to_certifyedge.json --out trace_certificate.json && labtrust attach-certificate ...",
		}}
	case "artifact_registry_admission":
		errMsg, _ := c.Details["error"].(string)
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: ComponentProvabilityFabric,
			RepairHint:           "Ensure ArtifactRegistry.v0 lists all bundle component types with matching producer and allowed statuses.",
			RegenerateCmd:        "pf verify science-claim <bundle> --handoff handoff_to_pf.json --registry artifact_registry.json --release-mode",
			Expected:             "registry admission passes",
			Actual:               errMsg,
		}}
	case "source_commit_not_placeholder":
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: ComponentProvabilityFabric,
			RepairHint:           "Set PF_SOURCE_COMMIT to the current PF git commit and re-run verify/sign in release mode.",
			RegenerateCmd:        "export PF_SOURCE_COMMIT=$(git rev-parse HEAD) && pf verify science-claim <bundle> --release-mode --handoff handoff_to_pf.json --registry artifact_registry.json",
		}}
	default:
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: responsibleComponentForReason(code),
			RepairHint:           defaultVerificationRepair(code, c.Description),
			Actual:               c.Description,
		}}
	}
}

func explainReleaseChainCheck(c ReleaseValidationCheck) []FailureExplanation {
	code, _ := c.Details["failure_code"].(string)
	switch c.CheckID {
	case "manifest_hashes_match":
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: "pcs-core",
			RepairHint:           "Regenerate the release manifest from pcs-core or re-sync fixtures so artifact sha256 pins match on-disk files.",
			RegenerateCmd:        "make sync-pcs-rc-fixtures",
		}}
	case "registry_admission_passed", "registry_artifact_registered", "registry_schema_matches",
		"registry_producer_allowed", "registry_status_allowed", "registry_required_fields_present",
		"registry_semantic_checks_executed":
		errMsg, _ := c.Details["error"].(string)
		if errMsg == "" {
			errMsg = fmt.Sprint(c.Details)
		}
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: ComponentProvabilityFabric,
			RepairHint:           "Pass ArtifactRegistry.v0 via --registry and ensure every manifest artifact type is registered with matching schema, producer, and required fields.",
			RegenerateCmd:        "pf verify release-chain --manifest release_manifest.v0.json --registry artifact_registry.json --artifact-dir <dir> --release-mode",
			Actual:               errMsg,
		}}
	case "signed_input_bundle_hash_match":
		exp, _ := c.Details["expected"].(string)
		act, _ := c.Details["actual"].(string)
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ArtifactPath:         "signed_science_claim_bundle.json",
			ResponsibleComponent: ComponentProvabilityFabric,
			Expected:             exp,
			Actual:               act,
			RepairHint:           "Re-sign the certified bundle with PF after verification passes.",
			RegenerateCmd:        "pf sign science-claim science_claim_bundle.certified.json --handoff handoff_to_pf.json --registry artifact_registry.json --out signed_science_claim_bundle.json --release-mode",
		}}
	default:
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			ResponsibleComponent: responsibleComponentForReason(code),
			RepairHint:           defaultReleaseChainRepair(code, c.Description),
			Actual:               c.Description,
		}}
	}
}

func responsibleComponentForReason(code string) string {
	switch code {
	case ReasonTraceHashMismatch, ReasonCertificateNotChecked, ReasonCertificateRejected:
		return "CertifyEdge"
	case ReasonRegistryAdmissionFailed:
		return ComponentProvabilityFabric
	case ReasonHandoffInvalid, FailureCodeLegacyHandoffForbiddenInReleaseMode:
		return ComponentLabTrustGym
	default:
		return ComponentProvabilityFabric
	}
}

func defaultVerificationRepair(code, desc string) string {
	if code != "" {
		return fmt.Sprintf("Resolve %s: %s", code, desc)
	}
	return desc
}

func defaultReleaseChainRepair(code, desc string) string {
	if code != "" {
		return fmt.Sprintf("Resolve %s: %s", code, desc)
	}
	return desc
}

// FormatFailureExplanations renders explanations for CLI output.
func FormatFailureExplanations(explanations []FailureExplanation) string {
	var b strings.Builder
	for i, e := range explanations {
		if i > 0 {
			b.WriteString("\n")
		}
		b.WriteString("check: ")
		b.WriteString(e.CheckID)
		if e.ResponsibleComponent != "" {
			b.WriteString("\ncomponent: ")
			b.WriteString(e.ResponsibleComponent)
		}
		if e.ArtifactPath != "" {
			b.WriteString("\nartifact: ")
			b.WriteString(e.ArtifactPath)
		}
		if e.Expected != "" {
			b.WriteString("\nexpected: ")
			b.WriteString(e.Expected)
		}
		if e.Actual != "" {
			b.WriteString("\nactual: ")
			b.WriteString(e.Actual)
		}
		b.WriteString("\nrepair: ")
		b.WriteString(e.RepairHint)
		if e.RegenerateCmd != "" {
			b.WriteString("\nregenerate: ")
			b.WriteString(e.RegenerateCmd)
		}
	}
	return b.String()
}
