// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import "strings"

// DeferredRegistryCheck records registry semantic coverage deferred outside the release-chain catalog.
type DeferredRegistryCheck struct {
	RegistryRef          string `json:"registry_ref"`
	Status               string `json:"status"`
	EnforcementLocation  string `json:"enforcement_location"`
	ResponsibleComponent string `json:"responsible_component"`
	Reason               string `json:"reason"`
}

// BuildDeferredRegistryChecks derives deferred_registry_checks from release-chain audit records.
func BuildDeferredRegistryChecks(checks []ReleaseValidationCheck) []DeferredRegistryCheck {
	seen := make(map[string]struct{})
	var out []DeferredRegistryCheck
	for _, c := range checks {
		exec, _ := c.Details["execution"].(string)
		switch exec {
		case RegistryExecutionDeferred:
			ref := registryRefFromCheck(c)
			if ref == "" {
				continue
			}
			if _, dup := seen[ref]; dup {
				continue
			}
			seen[ref] = struct{}{}
			reason, _ := c.Details["deferral_reason"].(string)
			if reason == "" {
				reason = "Registry semantic check deferred to cited enforcement location."
			}
			responsible, _ := c.Details["responsible_component"].(string)
			if responsible == "" {
				responsible = ComponentProvabilityFabric
			}
			out = append(out, DeferredRegistryCheck{
				RegistryRef:          ref,
				Status:               "deferred",
				EnforcementLocation:  enforcementLocationForDeferred(c),
				ResponsibleComponent: responsible,
				Reason:               reason,
			})
		case RegistryExecutionSkippedNonRelease:
			ref := registryRefFromCheck(c)
			if ref == "" {
				continue
			}
			if _, dup := seen[ref]; dup {
				continue
			}
			seen[ref] = struct{}{}
			responsible, _ := c.Details["responsible_component"].(string)
			if responsible == "" {
				responsible = ComponentProvabilityFabric
			}
			out = append(out, DeferredRegistryCheck{
				RegistryRef:          ref,
				Status:               "skipped",
				EnforcementLocation:  "registry_metadata",
				ResponsibleComponent: responsible,
				Reason:               "Registry semantic check skipped outside release mode.",
			})
		}
	}
	if out == nil {
		return []DeferredRegistryCheck{}
	}
	return out
}

func registryRefFromCheck(c ReleaseValidationCheck) string {
	if ref, _ := c.Details["registry_check_ref"].(string); ref != "" {
		return ref
	}
	if len(c.RegistryCheckRefs) > 0 {
		return c.RegistryCheckRefs[0]
	}
	if strings.HasPrefix(c.CheckID, "registry.") {
		return c.CheckID
	}
	return ""
}

func enforcementLocationForDeferred(c ReleaseValidationCheck) string {
	if enforcedBy, _ := c.Details["enforced_by"].(string); enforcedBy != "" {
		if strings.HasPrefix(enforcedBy, "registry.") || enforcedBy == "admission_profile_enforcement" {
			return "artifact_validate"
		}
		return "release_chain"
	}
	if strings.HasPrefix(c.CheckID, "registry.") {
		return "artifact_validate"
	}
	return "release_chain"
}
