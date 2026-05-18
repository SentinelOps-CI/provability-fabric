// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"path/filepath"
	"strings"
)

// Registry semantic check execution outcomes recorded in ReleaseChainValidationResult.v0.
const (
	RegistryExecutionPassed          = "executed_passed"
	RegistryExecutionFailed          = "executed_failed"
	RegistryExecutionDeferred        = "deferred_with_reason"
	RegistryExecutionSkippedNonRelease = "skipped_non_release"
)

// RegistrySemanticDeferral documents why PF defers a registry semantic check at release-chain time.
type RegistrySemanticDeferral struct {
	Reason               string
	EnforcedBy           string
	ReleaseModeAllowed   bool
	ResponsibleComponent string
}

var registrySemanticDeferralCatalog = map[string]RegistrySemanticDeferral{
	"artifact_hashes_match_files": {
		Reason:               "PF validates manifest artifact sha256 pins against on-disk files",
		EnforcedBy:           "manifest_hashes_match",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"verified_input_bundle_hash_matches_certified": {
		Reason:               "PF verifies certified bundle hash via science-claim verification and handoff invariants",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"signed_input_bundle_hash_matches_certified": {
		Reason:               "PF compares signed_science_claim_bundle input hash to certified bundle file digest",
		EnforcedBy:           "signed_input_bundle_hash_match",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"embedded_bundle_passes_science_claim_semantics": {
		Reason:               "PF runs full ScienceClaimBundle verification on the embedded certified bundle",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"failed_checks_block_import_ready_status": {
		Reason:               "PF verification result status and failed_checks are enforced during science-claim verify",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"status_matches_check_outcomes": {
		Reason:               "PF maps verification check outcomes to ProofChecked/Rejected status policy",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"handoff_input_hashes_when_validated": {
		Reason:               "PF validates HandoffManifest.v0 input artifact sha256 pins at science-claim admission",
		EnforcedBy:           "handoff_manifest_validated",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"non_empty_runtime_receipts": {
		Reason:               "PF science-claim verification requires at least one runtime receipt",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"certified_bundle_has_certificate_when_checked": {
		Reason:               "PF certificate_id_consistent and certificate status checks cover certified bundle certificates",
		EnforcedBy:           "certificate_id_consistent",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"assumption_set_ref_present": {
		Reason:               "PF science-claim bundle semantic checks validate assumption_set_ref",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"certificate_refs_resolve": {
		Reason:               "PF evidence_refs_complete check validates certificate references",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"trace_hash_matches_runtime_receipt": {
		Reason:               "PF trace_hash_consistent release-chain check aligns certificate and receipt trace hashes",
		EnforcedBy:           "trace_hash_consistent",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"trace_hash_present": {
		Reason:               "PF trace_hash_consistent requires a non-empty runtime receipt trace_hash",
		EnforcedBy:           "trace_hash_consistent",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"status_is_certificate_checked_for_release": {
		Reason:               "PF certificate status policy is enforced during science-claim verification",
		EnforcedBy:           "science_claim_bundle_verification",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"source_commit_matches_release_manifest": {
		Reason:               "PF producer_commits_match validates manifest producer repo pins",
		EnforcedBy:           "producer_commits_match",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"release_mode_commit_policy": {
		Reason:               "PF release-mode rejects placeholder commits on manifest and verification outputs",
		EnforcedBy:           "producer_commits_match",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
	"entries_cover_required_artifact_types": {
		Reason:               "ArtifactRegistry.v0 is validated at PF admission; manifest types are checked via registry_artifact_registered",
		EnforcedBy:           "registry_artifact_registered",
		ReleaseModeAllowed:   true,
		ResponsibleComponent: ComponentProvabilityFabric,
	},
}

// RegistrySemanticAuditContext inputs for per-check registry semantic audit records.
type RegistrySemanticAuditContext struct {
	Manifest *ReleaseManifest
	Registry *ArtifactRegistry
	BaseDir  string
	Bundle   *ScienceClaimBundle
	Opts     RegistryValidateOptions
}

func registrySemanticCheckID(artifactType, checkID string) string {
	return fmt.Sprintf("registry.%s.%s", artifactType, checkID)
}

// CollectRegistrySemanticChecks emits one ReleaseValidationCheck per registry semantic check.
func CollectRegistrySemanticChecks(ctx RegistrySemanticAuditContext) []ReleaseValidationCheck {
	if ctx.Registry == nil || ctx.Manifest == nil {
		return nil
	}
	seen := make(map[string]struct{})
	var out []ReleaseValidationCheck
	for artifactType := range registryAuditArtifactTypes(ctx) {
		regEntry, ok := ctx.Registry.entryByArtifactType(artifactType)
		if !ok {
			continue
		}
		for _, check := range regEntry.SemanticChecks {
			id := registrySemanticCheckID(regEntry.ArtifactType, check.CheckID)
			if _, dup := seen[id]; dup {
				continue
			}
			seen[id] = struct{}{}
			out = append(out, auditRegistrySemanticCheck(ctx, regEntry, check))
		}
	}
	return out
}

func registryAuditArtifactTypes(ctx RegistrySemanticAuditContext) map[string]struct{} {
	types := make(map[string]struct{})
	for _, name := range pfReleaseChainArtifactNames(ctx.Manifest) {
		types[ctx.Manifest.Artifacts[name].ArtifactType] = struct{}{}
	}
	if ctx.Bundle != nil {
		for _, comp := range bundleRegistryComponents(ctx.Bundle) {
			types[comp.artifactType] = struct{}{}
		}
	}
	return types
}

func auditRegistrySemanticCheck(ctx RegistrySemanticAuditContext, regEntry RegistryEntry, check RegistrySemanticCheckRef) ReleaseValidationCheck {
	id := registrySemanticCheckID(regEntry.ArtifactType, check.CheckID)
	responsible := check.ResponsibleComponent
	if responsible == "" {
		responsible = regEntry.Producer
	}
	releaseBlocking := isReleaseBlockingSeverity(check.Severity)
	baseDetails := map[string]any{
		"artifact_type":         regEntry.ArtifactType,
		"responsible_component": responsible,
		"registry_check_id":     check.CheckID,
		"release_blocking":      releaseBlocking,
		"severity":              check.Severity,
	}
	if !ctx.Opts.ReleaseMode {
		baseDetails["execution"] = RegistryExecutionSkippedNonRelease
		return ReleaseValidationCheck{
			CheckID:     id,
			Description: fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
			Status:      "skipped",
			Details:     baseDetails,
		}
	}
	if ctx.Bundle != nil {
		executed, err := runRegistrySemanticCheck(ctx.Bundle, check.CheckID)
		if executed {
			if err != nil {
				baseDetails["execution"] = RegistryExecutionFailed
				baseDetails["error"] = err.Error()
				return releaseFailCheck(id,
					fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
					ReasonRegistryAdmissionFailed, baseDetails)
			}
			baseDetails["execution"] = RegistryExecutionPassed
			return releasePassCheck(id,
				fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
				baseDetails)
		}
	}
	if manifestRegistrySemanticDeferred(check.CheckID) || isRegistrySemanticDeferred(check.CheckID) {
		deferral, ok := registrySemanticDeferralCatalog[check.CheckID]
		if !ok {
			baseDetails["execution"] = RegistryExecutionDeferred
			return releaseFailCheck(id,
				fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
				ReasonRegistryAdmissionFailed, mergeDetails(baseDetails, map[string]any{
					"deferral_reason":        "no deferral catalog entry",
					"release_mode_allowed":   false,
				}))
		}
		baseDetails["execution"] = RegistryExecutionDeferred
		baseDetails["deferral_reason"] = deferral.Reason
		baseDetails["enforced_by"] = deferral.EnforcedBy
		baseDetails["release_mode_allowed"] = deferral.ReleaseModeAllowed
		if deferral.ResponsibleComponent != "" {
			baseDetails["responsible_component"] = deferral.ResponsibleComponent
		}
		status := "passed"
		if !deferral.ReleaseModeAllowed && ctx.Opts.ReleaseMode && !ctx.Opts.AllowSkippedRegistrySemantics {
			status = "failed"
			baseDetails["failure_code"] = ReasonRegistryAdmissionFailed
		}
		return ReleaseValidationCheck{
			CheckID:           id,
			Description:       fmt.Sprintf("Registry semantic check %s deferred for %s", check.CheckID, regEntry.ArtifactType),
			Status:            status,
			Details:           baseDetails,
			RegistryCheckRefs: []string{check.CheckID},
		}
	}
	executed, err := runManifestRegistrySemantic(check.CheckID, ctx.Manifest, "", ManifestArtifactEntry{})
	if executed {
		if err != nil {
			baseDetails["execution"] = RegistryExecutionFailed
			baseDetails["error"] = err.Error()
			return releaseFailCheck(id,
				fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
				ReasonRegistryAdmissionFailed, baseDetails)
		}
		baseDetails["execution"] = RegistryExecutionPassed
		return releasePassCheck(id,
			fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
			baseDetails)
	}
	baseDetails["execution"] = RegistryExecutionDeferred
	code := FailureCodeReleaseModeRegistryCheckUnregistered
	if releaseBlocking {
		code = ReasonRegistryAdmissionFailed
	}
	return releaseFailCheck(id,
		fmt.Sprintf("Registry semantic check %s for %s", check.CheckID, regEntry.ArtifactType),
		code, mergeDetails(baseDetails, map[string]any{
			"deferral_reason":      "registry semantic check not implemented or catalogued",
			"enforced_by":          "",
			"release_mode_allowed": false,
		}))
}

func isReleaseBlockingSeverity(severity string) bool {
	switch strings.ToLower(strings.TrimSpace(severity)) {
	case "release_blocking", "required", "producer_responsible":
		return true
	default:
		return false
	}
}

func isRegistrySemanticDeferred(checkID string) bool {
	_, ok := registrySemanticDeferralCatalog[checkID]
	return ok
}

func mergeDetails(base map[string]any, extra map[string]any) map[string]any {
	out := make(map[string]any, len(base)+len(extra))
	for k, v := range base {
		out[k] = v
	}
	for k, v := range extra {
		out[k] = v
	}
	return out
}

func loadCertifiedBundleForAudit(baseDir string) *ScienceClaimBundle {
	if strings.TrimSpace(baseDir) == "" {
		return nil
	}
	path := filepath.Join(baseDir, "science_claim_bundle.certified.json")
	bundle, err := LoadScienceClaimBundle(path)
	if err != nil {
		return nil
	}
	return bundle
}

func registrySemanticChecksFromResult(checks []ReleaseValidationCheck) []ReleaseValidationCheck {
	var out []ReleaseValidationCheck
	for _, c := range checks {
		if strings.HasPrefix(c.CheckID, "registry.") {
			out = append(out, c)
		}
	}
	return out
}

// HasUnexplainedDeferredRegistryCheckForTest exposes release-mode deferral policy for tests.
func HasUnexplainedDeferredRegistryCheckForTest(checks []ReleaseValidationCheck, releaseMode bool, allowSkipped bool) bool {
	return hasUnexplainedDeferredRegistryCheck(checks, releaseMode, allowSkipped)
}

func hasUnexplainedDeferredRegistryCheck(checks []ReleaseValidationCheck, releaseMode bool, allowSkipped bool) bool {
	if !releaseMode || allowSkipped {
		return false
	}
	for _, c := range registrySemanticChecksFromResult(checks) {
		exec, _ := c.Details["execution"].(string)
		if exec == RegistryExecutionSkippedNonRelease {
			if blocking, _ := c.Details["release_blocking"].(bool); blocking {
				return true
			}
		}
		if exec != RegistryExecutionDeferred {
			if exec == RegistryExecutionFailed || c.Status == "failed" {
				continue
			}
			continue
		}
		reason, _ := c.Details["deferral_reason"].(string)
		enforcedBy, _ := c.Details["enforced_by"].(string)
		allowed, _ := c.Details["release_mode_allowed"].(bool)
		if strings.TrimSpace(reason) == "" || strings.TrimSpace(enforcedBy) == "" || !allowed {
			return true
		}
		if c.Status == "failed" {
			return true
		}
	}
	return false
}

func ValidateRegistrySemanticCheckRecords(checks []ReleaseValidationCheck) error {
	for _, c := range registrySemanticChecksFromResult(checks) {
		exec, _ := c.Details["execution"].(string)
		if exec != RegistryExecutionDeferred {
			continue
		}
		reason, _ := c.Details["deferral_reason"].(string)
		enforcedBy, _ := c.Details["enforced_by"].(string)
		if strings.TrimSpace(reason) == "" || strings.TrimSpace(enforcedBy) == "" {
			return fmt.Errorf("deferred registry check %q missing deferral_reason or enforced_by", c.CheckID)
		}
		if _, ok := c.Details["release_mode_allowed"]; !ok {
			return fmt.Errorf("deferred registry check %q missing release_mode_allowed", c.CheckID)
		}
	}
	return nil
}
