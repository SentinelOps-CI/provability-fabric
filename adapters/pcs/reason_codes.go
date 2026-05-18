// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// Stable reason codes for Scientific Memory and operator tooling.
const (
	ReasonSchemaInvalid              = "PCS_SCHEMA_INVALID"
	ReasonArtifactMissing            = "PCS_ARTIFACT_MISSING"
	ReasonAssumptionRefMismatch      = "PCS_ASSUMPTION_REF_MISMATCH"
	ReasonTraceHashMissing           = "PCS_TRACE_HASH_MISSING"
	ReasonTraceHashMismatch          = "PCS_TRACE_HASH_MISMATCH"
	ReasonCertificateNotChecked      = "PCS_CERTIFICATE_NOT_CHECKED"
	ReasonCertificateRejected        = "PCS_CERTIFICATE_REJECTED"
	ReasonEvidenceRefsIncomplete     = "PCS_EVIDENCE_REFS_INCOMPLETE"
	ReasonEvidenceRefUnknown         = "PCS_EVIDENCE_REF_UNKNOWN"
	ReasonArtifactStale              = "PCS_ARTIFACT_STALE"
	ReasonSourceProvenanceMissing      = "PCS_SOURCE_PROVENANCE_MISSING"
	ReasonSignatureMissing           = "PCS_SIGNATURE_MISSING"
	ReasonSourceCommitPlaceholder    = "PCS_SOURCE_COMMIT_PLACEHOLDER"
	ReasonLegacyBundleFormat         = "PCS_LEGACY_BUNDLE_FORMAT"
	ReasonRuntimeReceiptCount        = "PCS_RUNTIME_RECEIPT_COUNT"
	ReasonIllegalStatusTransition    = "PCS_ILLEGAL_STATUS_TRANSITION"
	ReasonRegistryAdmissionFailed    = "PCS_REGISTRY_ADMISSION_FAILED"
	ReasonHandoffInvalid             = "PCS_HANDOFF_INVALID"
	ReasonLegacyHandoffForbidden     = "legacy_handoff_forbidden_in_release_mode"
)

// Release-mode admission failure codes (precise operator signals).
const (
	FailureCodeReleaseModeHandoffRequired      = "release_mode_handoff_required"
	FailureCodeReleaseModeRegistryRequired     = "release_mode_registry_required"
	FailureCodeReleaseModeManifestRequired     = "release_mode_manifest_required"
	FailureCodeReleaseModeHandoffKindMismatch  = "release_mode_handoff_kind_mismatch"
	FailureCodeReleaseModeCertificateRequired  = "release_mode_certificate_required"
	FailureCodeReleaseModeBundleRequired       = "release_mode_bundle_required"
	FailureCodeReleaseModeProfileRejected      = "release_mode_profile_rejected"
	FailureCodeReleaseModeLocalDevForbidden    = "release_mode_local_dev_forbidden"
	FailureCodeReleaseModeRegistryCheckSkipped = "release_mode_registry_check_skipped"
	FailureCodeReleaseModeRegistryCheckUnregistered = "release_mode_registry_check_unregistered"
	FailureCodeMissingAdmissionProfile              = "missing_admission_profile"
	FailureCodeUnknownAdmissionProfile              = "unknown_admission_profile"
	FailureCodeMissingToolUseTrace                  = "missing_tool_use_trace"
	FailureCodeMissingToolUseCertificate            = "missing_tool_use_certificate"
	FailureCodeToolUseCertificateRejected           = "tool_use_certificate_rejected"
	FailureCodeToolTraceHashMismatch                = "tool_trace_hash_mismatch"
	FailureCodeUnauthorizedToolCallViolation        = "unauthorized_tool_call_certificate_violation"
	FailureCodeToolUseReleaseNotImplemented         = "tool_use_release_not_implemented"
	FailureCodeRegistryCheckMissingResponsible      = "registry_check_missing_responsible_component"
	FailureCodeRegistryCheckNotInResult             = "registry_check_not_in_release_chain_result"
)

func withReason(code string, details map[string]any) map[string]any {
	if details == nil {
		details = map[string]any{}
	}
	details["reason_code"] = code
	return details
}
