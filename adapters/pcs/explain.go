// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// FailureExplanation is one actionable failure line for operators.
type FailureExplanation struct {
	CheckID       string `json:"check_id"`
	ArtifactPath  string `json:"artifact_path,omitempty"`
	Expected      string `json:"expected,omitempty"`
	Actual        string `json:"actual,omitempty"`
	RepairHint    string `json:"repair_hint"`
	RegenerateCmd string `json:"regenerate_command,omitempty"`
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
			CheckID:       c.CheckID,
			RepairHint:    "Re-export trace and runtime receipt from LabTrust, re-run CertifyEdge, and re-attach the certificate.",
			RegenerateCmd: "labtrust export-trace ... && certifyedge emit-pcs-certificate ... && labtrust attach-certificate ...",
		}}
	case "artifact_registry_admission":
		errMsg, _ := c.Details["error"].(string)
		return []FailureExplanation{{
			CheckID:       c.CheckID,
			RepairHint:    "Ensure ArtifactRegistry.v0 lists all bundle component types with matching producer and allowed statuses.",
			RegenerateCmd: "pf verify science-claim <bundle> --handoff <handoff> --registry <artifact_registry.json> --release-mode",
			Expected:      "registry admission passes",
			Actual:        errMsg,
		}}
	case "source_commit_not_placeholder":
		return []FailureExplanation{{
			CheckID:       c.CheckID,
			RepairHint:    "Set PF_SOURCE_COMMIT to the current PF git commit and re-run verify/sign in release mode.",
			RegenerateCmd: "export PF_SOURCE_COMMIT=$(git rev-parse HEAD) && pf verify science-claim <bundle> --release-mode --handoff <handoff> --registry <registry>",
		}}
	default:
		return []FailureExplanation{{
			CheckID:    c.CheckID,
			RepairHint: defaultVerificationRepair(code, c.Description),
			Actual:     c.Description,
		}}
	}
}

func explainReleaseChainCheck(c ReleaseValidationCheck) []FailureExplanation {
	code, _ := c.Details["failure_code"].(string)
	switch c.CheckID {
	case "manifest_hashes_match":
		return []FailureExplanation{{
			CheckID:       c.CheckID,
			RepairHint:    "Regenerate the release manifest from pcs-core or re-sync fixtures so artifact sha256 pins match on-disk files.",
			RegenerateCmd: "make sync-pcs-rc-fixtures",
		}}
	case "registry_admission_passed":
		errMsg, _ := c.Details["error"].(string)
		return []FailureExplanation{{
			CheckID:       c.CheckID,
			RepairHint:    "Pass ArtifactRegistry.v0 via --registry and ensure every manifest artifact type is registered.",
			RegenerateCmd: "pf verify release-chain --manifest release_manifest.v0.json --registry artifact_registry.json --artifact-dir <dir> --release-mode",
			Actual:        errMsg,
		}}
	case "signed_input_bundle_hash_match":
		exp, _ := c.Details["expected"].(string)
		act, _ := c.Details["actual"].(string)
		return []FailureExplanation{{
			CheckID:       c.CheckID,
			ArtifactPath:  "signed_science_claim_bundle.json",
			Expected:      exp,
			Actual:        act,
			RepairHint:    "Re-sign the certified bundle with PF after verification passes.",
			RegenerateCmd: "pf sign science-claim science_claim_bundle.certified.json --handoff handoff_to_pf.json --out signed_science_claim_bundle.json --release-mode",
		}}
	default:
		return []FailureExplanation{{
			CheckID:    c.CheckID,
			RepairHint: defaultReleaseChainRepair(code, c.Description),
			Actual:     c.Description,
		}}
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
