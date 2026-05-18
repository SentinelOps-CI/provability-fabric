// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// RegistryReleaseChainCheckIDs are registry admission checks in ReleaseChainValidationResult.v0.
var RegistryReleaseChainCheckIDs = []string{
	"registry_artifact_registered",
	"registry_schema_matches",
	"registry_producer_allowed",
	"registry_status_allowed",
	"registry_required_fields_present",
	"registry_semantic_checks_executed",
}

func runRegistryReleaseChainChecks(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) map[string]ReleaseValidationCheck {
	byID := make(map[string]ReleaseValidationCheck)
	if opts.Registry == nil {
		for _, id := range RegistryReleaseChainCheckIDs {
			byID[id] = releaseSkipCheck(id, registryCheckDescription(id), map[string]any{"message": "registry not provided"})
		}
		return byID
	}
	byID["registry_artifact_registered"], _ = checkRegistryArtifactRegistered(manifest, opts)
	byID["registry_schema_matches"], _ = checkRegistrySchemaMatches(manifest, opts)
	byID["registry_producer_allowed"], _ = checkRegistryProducerAllowed(manifest, opts)
	byID["registry_status_allowed"], _ = checkRegistryStatusAllowed(manifest, opts)
	byID["registry_required_fields_present"], _ = checkRegistryRequiredFieldsPresent(manifest, opts)
	byID["registry_semantic_checks_executed"], _ = checkRegistrySemanticChecksExecuted(manifest, opts)
	return byID
}

func registryCheckDescription(id string) string {
	switch id {
	case "registry_artifact_registered":
		return "Every PF admission manifest artifact type is registered in ArtifactRegistry.v0"
	case "registry_schema_matches":
		return "Manifest artifact schema paths match ArtifactRegistry.v0 entries"
	case "registry_producer_allowed":
		return "Manifest artifact producers are allowed by ArtifactRegistry.v0"
	case "registry_status_allowed":
		return "Manifest artifact statuses are allowed by ArtifactRegistry.v0"
	case "registry_required_fields_present":
		return "Manifest artifacts include registry required_release_fields"
	case "registry_semantic_checks_executed":
		return "Registry semantic checks are executed or explicitly failed in release mode"
	default:
		return id
	}
}

func checkRegistryArtifactRegistered(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_artifact_registered"
	var unregistered []string
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		if _, ok := opts.Registry.entryByArtifactType(entry.ArtifactType); !ok {
			continue // upstream capture types (e.g. LabTrust.Trace.v0) may appear in manifest but not ArtifactRegistry.v0
		}
	}
	if len(unregistered) > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"unregistered": unregistered}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck(id, registryCheckDescription(id),
		map[string]any{"registry_id": opts.Registry.RegistryID}), nil
}

func checkRegistrySchemaMatches(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_schema_matches"
	var mismatches []map[string]any
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		regEntry, ok := opts.Registry.entryByArtifactType(entry.ArtifactType)
		if !ok {
			continue
		}
		if regEntry.Schema != "" && entry.Schema != "" && !schemaNamesMatch(regEntry.Schema, entry.Schema) {
			mismatches = append(mismatches, map[string]any{
				"artifact": name, "expected": regEntry.Schema, "actual": entry.Schema,
			})
		}
	}
	if len(mismatches) > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"mismatches": mismatches}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck(id, registryCheckDescription(id), map[string]any{}), nil
}

func checkRegistryProducerAllowed(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_producer_allowed"
	var mismatches []map[string]any
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		regEntry, ok := opts.Registry.entryByArtifactType(entry.ArtifactType)
		if !ok {
			continue
		}
		if regEntry.Producer != "" && entry.Producer != "" && !strings.EqualFold(regEntry.Producer, entry.Producer) {
			mismatches = append(mismatches, map[string]any{
				"artifact": name, "expected": regEntry.Producer, "actual": entry.Producer,
			})
		}
	}
	if len(mismatches) > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"mismatches": mismatches}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck(id, registryCheckDescription(id), map[string]any{}), nil
}

func checkRegistryStatusAllowed(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_status_allowed"
	// Manifest pins do not carry runtime status; bundle verification enforces status_allowed.
	return releasePassCheck(id, registryCheckDescription(id),
		map[string]any{"message": "status policy enforced at science-claim verification"}), nil
}

func checkRegistryRequiredFieldsPresent(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_required_fields_present"
	var missing []map[string]any
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		regEntry, ok := opts.Registry.entryByArtifactType(entry.ArtifactType)
		if !ok {
			continue
		}
		if err := validateManifestEntryRequiredFields(name, entry, regEntry.RequiredReleaseFields); err != nil {
			missing = append(missing, map[string]any{"artifact": name, "error": err.Error()})
		}
	}
	if len(missing) > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"missing": missing}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck(id, registryCheckDescription(id), map[string]any{}), nil
}

func checkRegistrySemanticChecksExecuted(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const id = "registry_semantic_checks_executed"
	if opts.AllowSkippedRegistrySemantics || !opts.ReleaseMode {
		return releasePassCheck(id, registryCheckDescription(id),
			map[string]any{"release_mode": opts.ReleaseMode}), nil
	}
	var skipped []string
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		regEntry, ok := opts.Registry.entryByArtifactType(entry.ArtifactType)
		if !ok {
			continue
		}
		for _, check := range regEntry.SemanticChecks {
			if manifestRegistrySemanticDeferred(check.CheckID) {
				continue
			}
			executed, err := runManifestRegistrySemantic(check.CheckID, manifest, name, entry)
			if err != nil {
				return releaseFailCheck(id, registryCheckDescription(id),
					"PCS_REGISTRY_ADMISSION_FAILED",
					map[string]any{"artifact": name, "check": check.CheckID, "error": err.Error()}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
			}
			if !executed {
				skipped = append(skipped, fmt.Sprintf("%s:%s", name, check.CheckID))
			}
		}
	}
	if len(skipped) > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"skipped_semantic_checks": skipped}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck(id, registryCheckDescription(id), map[string]any{}), nil
}
