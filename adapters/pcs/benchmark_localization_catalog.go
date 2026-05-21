// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import "strings"

// benchmarkFailureCodeToComponent mirrors pcs-core benchmark_localization.FAILURE_CODE_TO_COMPONENT.
func benchmarkFailureCodeToComponent(code string) string {
	switch strings.TrimSpace(code) {
	case ReasonTraceHashMismatch, "trace_hash_mismatch":
		return "hashing"
	case "signed_input_bundle_hash_match", "signed_input_hash_mismatch", "verified_input_hash_mismatch",
		"manifest_hash_mismatch", "bundle_hash_mismatch", "result_hash_mismatch", "dataset_hash_mismatch",
		"policy_hash_mismatch", "witness_hash_mismatch", "environment_digest_mismatch":
		return "hashing"
	case ReasonCertificateRejected, "rejected_certificate":
		return "certificate_producer"
	case FailureCodeScientificMemoryImportFailed:
		return "scientific_memory"
	case FailureCodeLegacyHandoffForbiddenInReleaseMode, "legacy_handoff_file", "legacy_handoff_in_release_mode":
		return "handoff"
	case FailureCodeReleaseModeHandoffRequired, "missing_handoff":
		return "handoff"
	case FailureCodeReleaseModeRegistryRequired, "missing_registry", ReasonRegistryAdmissionFailed:
		return "registry"
	case FailureCodeMissingLeanCheckResult, FailureCodeLeanCheckFailed, FailureCodeLeanReleaseIDMismatch,
		FailureCodeUnauthorizedLeanTheorem, "missing_proof_obligation", "failed_lean_check", "failed_lean_theorem":
		return "formal_kernel"
	case FailureCodeReleaseModeManifestRequired, "manifest_missing", "artifact_missing":
		return "release_manifest"
	case FailureCodeAdmissionProfileWorkflowMismatch, "wrong_admission_profile":
		return "verifier"
	default:
		return ""
	}
}
