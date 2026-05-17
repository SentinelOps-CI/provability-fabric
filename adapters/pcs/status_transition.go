// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
)

// CheckStatusTransitionPolicy enforces PCS status transition rules before emitting ProofChecked.
func CheckStatusTransitionPolicy(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "status_transition_policy"
	if bundle == nil {
		return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
			ReasonIllegalStatusTransition, detailMsg("bundle missing"))
	}
	for i, cert := range bundle.Certificates {
		if cert == nil {
			continue
		}
		switch cert.Status {
		case StatusRejected:
			return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
				ReasonIllegalStatusTransition, map[string]any{
					"artifact": "trace_certificate",
					"from":     cert.Status,
					"to":       StatusProofChecked,
				})
		case StatusStale:
			return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
				ReasonIllegalStatusTransition, map[string]any{
					"artifact": "trace_certificate",
					"from":     cert.Status,
					"to":       StatusProofChecked,
				})
		case StatusCertificateChecked:
			// allowed path
		default:
			return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
				ReasonIllegalStatusTransition, map[string]any{
					"certificate_index": i,
					"from":              cert.Status,
					"to":                StatusProofChecked,
				})
		}
	}
	if claim := bundle.ClaimArtifact; claim != nil {
		switch claim.Status {
		case StatusRejected, StatusStale:
			return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
				ReasonIllegalStatusTransition, map[string]any{
					"artifact": "claim_artifact",
					"from":     claim.Status,
					"to":       StatusProofChecked,
				})
		case StatusRuntimeObserved:
			if !certificateCheckedPresent(bundle) {
				return failCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states",
					ReasonIllegalStatusTransition, map[string]any{
						"artifact": "claim_artifact",
						"from":     claim.Status,
						"to":       StatusProofChecked,
						"message":  "RuntimeObserved cannot reach ProofChecked without CertificateChecked",
					})
			}
		}
	}
	return passCheck(id, "PCS status transitions allow ProofChecked only from admissible certificate states", map[string]any{})
}

func certificateCheckedPresent(bundle *ScienceClaimBundle) bool {
	for _, cert := range bundle.Certificates {
		if cert != nil && cert.Status == StatusCertificateChecked {
			return true
		}
	}
	return false
}

// AssertAdmissibleForProofChecked is a hard error wrapper for sign/verify admission.
func AssertAdmissibleForProofChecked(bundle *ScienceClaimBundle) error {
	check := CheckStatusTransitionPolicy(bundle)
	if check.Status == CheckFailed {
		code, _ := check.Details["reason_code"].(string)
		if code == "" {
			code = ReasonIllegalStatusTransition
		}
		return fmt.Errorf("%s: %s", code, check.Description)
	}
	return nil
}
