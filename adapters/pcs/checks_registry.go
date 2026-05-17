// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// RequiredCheckIDs is the ordered v0.1 verification checklist (15 checks).
var RequiredCheckIDs = []string{
	"science_claim_bundle_schema",
	"claim_artifact_present",
	"assumption_set_present",
	"runtime_receipt_present",
	"trace_certificate_present",
	"evidence_bundle_present",
	"assumption_set_ref_match",
	"runtime_trace_hash_present",
	"trace_hash_alignment",
	"certificate_status_checked",
	"evidence_refs_complete",
	"artifact_not_stale",
	"source_provenance_present",
	"signature_or_digest_present",
	"source_commit_not_placeholder",
}

// NormalizeChecks enforces RequiredCheckIDs order and returns an error if any ID is missing.
func NormalizeChecks(checks []VerificationCheck) ([]VerificationCheck, error) {
	byID := make(map[string]VerificationCheck, len(checks))
	for _, c := range checks {
		byID[c.CheckID] = c
	}
	ordered := make([]VerificationCheck, 0, len(RequiredCheckIDs))
	for _, id := range RequiredCheckIDs {
		c, ok := byID[id]
		if !ok {
			return nil, &MissingCheckError{CheckID: id}
		}
		ordered = append(ordered, c)
	}
	return ordered, nil
}

// MissingCheckError indicates the verification report omitted a required check.
type MissingCheckError struct {
	CheckID string
}

func (e *MissingCheckError) Error() string {
	return "missing required check: " + e.CheckID
}
