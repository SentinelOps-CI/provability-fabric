// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// CheckAssumptionSetRefMatch verifies ClaimArtifact.assumption_set_ref matches AssumptionSet.assumption_set_id.
func CheckAssumptionSetRefMatch(claim *ClaimArtifact, assumptions *AssumptionSet) VerificationCheck {
	const id = "assumption_set_ref_match"
	if claim == nil || assumptions == nil {
		return failCheck(id, "ClaimArtifact.assumption_set_ref matches AssumptionSet.assumption_set_id",
			ReasonArtifactMissing, detailMsg("claim or assumption set missing"))
	}
	ref := claim.AssumptionSetRef
	setID := assumptions.AssumptionSetID
	if ref == "" || setID == "" {
		return failCheck(id, "ClaimArtifact.assumption_set_ref matches AssumptionSet.assumption_set_id",
			ReasonAssumptionRefMismatch, map[string]any{"assumption_set_ref": ref, "assumption_set_id": setID})
	}
	if ref != setID {
		return failCheck(id, "ClaimArtifact.assumption_set_ref matches AssumptionSet.assumption_set_id",
			ReasonAssumptionRefMismatch, map[string]any{"assumption_set_ref": ref, "assumption_set_id": setID})
	}
	return passCheck(id, "ClaimArtifact.assumption_set_ref matches AssumptionSet.assumption_set_id",
		map[string]any{"assumption_set_ref": ref})
}
