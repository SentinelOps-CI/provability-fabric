// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// RequiredCheckIDs is the ordered v0.1 verification checklist (14 checks).
// Scientific Memory and snapshot tests depend on this stable ordering.
var RequiredCheckIDs = []string{
	"pcs.schema.science_claim_bundle",
	"pcs.presence.claim_artifact",
	"pcs.presence.assumption_set",
	"pcs.presence.runtime_receipt",
	"pcs.presence.trace_certificate",
	"pcs.presence.evidence_bundle",
	"pcs.claim.assumption_set_ref_match",
	"pcs.runtime.trace_hash_present",
	"pcs.certificate.trace_hash_match",
	"pcs.certificate.status_checked",
	"pcs.evidence.artifact_refs",
	"pcs.artifact.not_stale",
	"pcs.metadata.source_provenance",
	"pcs.metadata.signature_or_digest",
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
