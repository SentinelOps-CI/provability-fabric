// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"strings"
)

// EnrichReleaseChecksWithAudit adds failure_code, artifact_path, expected, actual, responsible_component, repair_hint to failed checks.
func EnrichReleaseChecksWithAudit(checks []ReleaseValidationCheck) []ReleaseValidationCheck {
	out := make([]ReleaseValidationCheck, len(checks))
	for i, c := range checks {
		out[i] = enrichFailedReleaseCheck(c)
	}
	return out
}

func enrichFailedReleaseCheck(c ReleaseValidationCheck) ReleaseValidationCheck {
	if c.Status != "failed" {
		return c
	}
	if c.Details == nil {
		c.Details = map[string]any{}
	}
	explanations := explainReleaseChainCheck(c)
	if len(explanations) == 0 {
		return c
	}
	e := explanations[0]
	if _, ok := c.Details["failure_code"]; !ok {
		if code, ok := c.Details["reason_code"].(string); ok && code != "" {
			c.Details["failure_code"] = code
		}
	}
	if e.ArtifactPath != "" {
		c.Details["artifact_path"] = e.ArtifactPath
	}
	if e.Expected != "" {
		c.Details["expected"] = e.Expected
	}
	if e.Actual != "" {
		c.Details["actual"] = e.Actual
	}
	if e.ResponsibleComponent != "" {
		c.Details["responsible_component"] = e.ResponsibleComponent
	}
	if e.RepairHint != "" {
		c.Details["repair_hint"] = e.RepairHint
	}
	if e.RegenerateCmd != "" {
		c.Details["regenerate_command"] = e.RegenerateCmd
	}
	if e.RegistryCheckRef != "" {
		c.Details["registry_check_ref"] = e.RegistryCheckRef
	}
	if e.HandoffRef != "" {
		c.Details["handoff_ref"] = e.HandoffRef
	}
	return c
}

func finalizeReleaseChainChecks(checks []ReleaseValidationCheck, profile *AdmissionProfile) []ReleaseValidationCheck {
	checks = EnrichReleaseChecksWithAudit(checks)
	if profile != nil {
		if err := ValidateProfileRequiredRegistryChecks(profile, checks); err != nil {
			checks = append(checks, releaseFailCheck("admission_profile_registry_checks",
				"Admission profile required_registry_checks satisfied",
				ReasonRegistryAdmissionFailed,
				map[string]any{"error": err.Error(), "profile_id": profile.ProfileID}))
		}
	}
	return checks
}

// ExplainReleaseChainReport is the JSON shape for pf explain release-chain --json.
type ExplainReleaseChainReport struct {
	Status       string               `json:"status"`
	Failed       []FailureExplanation `json:"failed"`
	Deferred     []FailureExplanation `json:"deferred,omitempty"`
	FailedCount  int                  `json:"failed_count"`
	DeferredCount int                 `json:"deferred_count"`
}

// BuildExplainReleaseChainReport builds structured explain output for CLI JSON mode.
func BuildExplainReleaseChainReport(result ReleaseChainValidationResult) ExplainReleaseChainReport {
	var failed, deferred []FailureExplanation
	for _, c := range result.Checks {
		if c.Status == "failed" {
			failed = append(failed, explainReleaseChainCheck(c)...)
			continue
		}
		if exec, _ := c.Details["execution"].(string); exec == RegistryExecutionDeferred {
			deferred = append(deferred, explainDeferredRegistryCheck(c)...)
		}
	}
	return ExplainReleaseChainReport{
		Status:        result.Status,
		Failed:        failed,
		Deferred:      deferred,
		FailedCount:   len(failed),
		DeferredCount: len(deferred),
	}
}

// FormatFailureExplanationsOperational renders engineer-friendly explain output.
func FormatFailureExplanationsOperational(explanations []FailureExplanation) string {
	var b strings.Builder
	for i, e := range explanations {
		if i > 0 {
			b.WriteString("\n\n")
		}
		b.WriteString("Failure\n")
		b.WriteString(e.CheckID)
		if e.FailureCode != "" {
			b.WriteString("\n\nFailure code\n")
			b.WriteString(e.FailureCode)
		}
		if e.RegistryCheckRef != "" {
			b.WriteString("\n\nRegistry check reference\n")
			b.WriteString(e.RegistryCheckRef)
		}
		if e.HandoffRef != "" {
			b.WriteString("\n\nHandoff reference\n")
			b.WriteString(e.HandoffRef)
		}
		b.WriteString("\n\nArtifact\n")
		if e.ArtifactPath != "" {
			b.WriteString(e.ArtifactPath)
		} else {
			b.WriteString("(see release chain validation result)")
		}
		if e.Expected != "" {
			b.WriteString("\n\nExpected\n")
			b.WriteString(e.Expected)
		}
		if e.Actual != "" {
			b.WriteString("\n\nActual\n")
			b.WriteString(e.Actual)
		}
		if e.ResponsibleComponent != "" {
			b.WriteString("\n\nResponsible component\n")
			b.WriteString(e.ResponsibleComponent)
		}
		b.WriteString("\n\nRepair\n")
		b.WriteString(e.RepairHint)
		if e.RegenerateCmd != "" {
			b.WriteString("\n\nCommand\n")
			b.WriteString(e.RegenerateCmd)
		}
	}
	return b.String()
}

// FormatExplainReportJSON marshals an explain report.
func FormatExplainReportJSON(v any) (string, error) {
	raw, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return "", err
	}
	return string(raw) + "\n", nil
}
