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
)

func withReason(code string, details map[string]any) map[string]any {
	if details == nil {
		details = map[string]any{}
	}
	details["reason_code"] = code
	return details
}
