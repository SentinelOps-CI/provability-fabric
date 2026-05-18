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
	FailureCode          string `json:"failure_code,omitempty"`
	ArtifactPath         string `json:"artifact_path,omitempty"`
	Expected             string `json:"expected,omitempty"`
	Actual               string `json:"actual,omitempty"`
	ResponsibleComponent string `json:"responsible_component,omitempty"`
	RegistryCheckRef     string `json:"registry_check_ref,omitempty"`
	HandoffRef           string `json:"handoff_ref,omitempty"`
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

// ExplainReleaseChainFailures returns repair hints for failed and deferred release-chain checks.
func ExplainReleaseChainFailures(result ReleaseChainValidationResult) []FailureExplanation {
	var out []FailureExplanation
	for _, c := range result.Checks {
		if c.Status == "failed" {
			out = append(out, explainReleaseChainCheck(c)...)
			continue
		}
		if exec, _ := c.Details["execution"].(string); exec == RegistryExecutionDeferred {
			out = append(out, explainDeferredRegistryCheck(c)...)
		}
	}
	return out
}

func explainDeferredRegistryCheck(c ReleaseValidationCheck) []FailureExplanation {
	reason, _ := c.Details["deferral_reason"].(string)
	enforcedBy, _ := c.Details["enforced_by"].(string)
	responsible, _ := c.Details["responsible_component"].(string)
	registryRef, _ := c.Details["registry_check_ref"].(string)
	if registryRef == "" {
		registryRef, _ = c.Details["registry_check_id"].(string)
	}
	allowed, _ := c.Details["release_mode_allowed"].(bool)
	hint := reason
	if enforcedBy != "" {
		hint = fmt.Sprintf("%s (enforced by release-chain check %s)", reason, enforcedBy)
	}
	regenerate := "pf verify release-chain --manifest release_manifest.v0.json --registry artifact_registry.json --artifact-dir <dir> --admission-profile labtrust_qc_release --release-mode"
	if strings.HasPrefix(c.CheckID, "registry.") {
		regenerate = "pf verify science-claim science_claim_bundle.certified.json --handoff handoff_to_pf.json --registry artifact_registry.json --admission-profile labtrust_qc_release --release-mode && " + regenerate
	}
	return []FailureExplanation{{
		CheckID:              c.CheckID,
		RegistryCheckRef:     registryRef,
		ResponsibleComponent: responsible,
		Expected:             fmt.Sprintf("deferral allowed in release mode=%v", allowed),
		Actual:               fmt.Sprintf("execution=%s", RegistryExecutionDeferred),
		RepairHint:           hint,
		RegenerateCmd:        regenerate,
	}}
}

func releaseCheckExplanationFields(c ReleaseValidationCheck) (failureCode, artifactPath, expected, actual, responsible, registryRef, handoffRef string) {
	failureCode, _ = c.Details["failure_code"].(string)
	artifactPath, _ = c.Details["artifact_path"].(string)
	expected, _ = c.Details["expected"].(string)
	actual, _ = c.Details["actual"].(string)
	responsible, _ = c.Details["responsible_component"].(string)
	registryRef, _ = c.Details["registry_check_ref"].(string)
	if registryRef == "" {
		registryRef, _ = c.Details["registry_check_id"].(string)
	}
	handoffRef, _ = c.Details["handoff_ref"].(string)
	if handoffRef == "" {
		handoffRef, _ = c.Details["handoff_id"].(string)
	}
	return
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
	fc, artifactPath, expected, actual, responsible, registryRef, handoffRef := releaseCheckExplanationFields(c)
	if strings.HasPrefix(c.CheckID, "registry.") {
		errMsg, _ := c.Details["error"].(string)
		exec, _ := c.Details["execution"].(string)
		exp := expected
		if exp == "" {
			exp = RegistryExecutionPassed
		}
		act := actual
		if act == "" {
			act = exec + ": " + errMsg
		}
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			FailureCode:          fc,
			ArtifactPath:         artifactPath,
			ResponsibleComponent: responsible,
			RegistryCheckRef:     registryRef,
			HandoffRef:           handoffRef,
			Expected:             exp,
			Actual:               act,
			RepairHint:           "Fix registry semantic check failure or update ArtifactRegistry.v0 semantic_checks for this artifact type.",
			RegenerateCmd:        "pf verify release-chain --manifest release_manifest.v0.json --registry artifact_registry.json --artifact-dir <dir> --admission-profile labtrust_qc_release --release-mode",
		}}
	}
	code := fc
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
	case "certificate_id_consistent":
		exp, _ := c.Details["expected"].(string)
		if exp == "" {
			exp, _ = c.Details["certificate_id"].(string)
		}
		act, _ := c.Details["actual"].(string)
		if act == "" {
			act, _ = c.Details["verification_result"].(string)
		}
		return []FailureExplanation{{
			CheckID:              "certificate_id_mismatch",
			ArtifactPath:         "science_claim_bundle.certified.json",
			ResponsibleComponent: ComponentLabTrustGym,
			Expected:             exp,
			Actual:               act,
			RepairHint:           "Regenerate the certified bundle from the current trace certificate.",
			RegenerateCmd:        "labtrust attach-certificate --trace trace.json --certificate trace_certificate.json --out science_claim_bundle.certified.json",
		}}
	default:
		act := actual
		if act == "" {
			act = c.Description
		}
		return []FailureExplanation{{
			CheckID:              c.CheckID,
			FailureCode:          fc,
			ArtifactPath:         artifactPath,
			ResponsibleComponent: responsible,
			RegistryCheckRef:     registryRef,
			HandoffRef:           handoffRef,
			Expected:             expected,
			Actual:               act,
			RepairHint:           defaultReleaseChainRepair(code, c.Description),
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
