// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// appendVerificationAdmissionChecks adds handoff, bundle verification, status, provenance, and signature checks to RCVR.
func appendVerificationAdmissionChecks(
	checks []ReleaseValidationCheck,
	failureCodes []string,
	handoff *HandoffManifest,
	bundleResult VerificationResult,
	opts ReleaseChainVerifyOptions,
) ([]ReleaseValidationCheck, []string) {
	if handoff != nil {
		checks, failureCodes = appendHandoffAdmissionChecks(checks, failureCodes, handoff, opts)
	}
	vrCheck := "science_claim_bundle_verification"
	if bundleResult.Status == StatusProofChecked {
		checks = append(checks, releasePassCheck(vrCheck,
			"ScienceClaimBundle verification reached ProofChecked",
			map[string]any{"verification_id": bundleResult.VerificationID}))
	} else {
		checks = append(checks, releaseFailCheck(vrCheck,
			"ScienceClaimBundle verification reached ProofChecked",
			"PCS_VERIFICATION_REJECTED", map[string]any{"status": bundleResult.Status}))
		failureCodes = append(failureCodes, "PCS_VERIFICATION_REJECTED")
	}
	for _, c := range bundleResult.Checks {
		mapped, codes := mapVerificationCheckToReleaseAdmission(c)
		if mapped.CheckID != "" {
			checks = append(checks, mapped)
			failureCodes = append(failureCodes, codes...)
		}
	}
	return checks, uniqueStrings(failureCodes)
}

func appendHandoffAdmissionChecks(
	checks []ReleaseValidationCheck,
	failureCodes []string,
	handoff *HandoffManifest,
	opts ReleaseChainVerifyOptions,
) ([]ReleaseValidationCheck, []string) {
	id := "handoff_manifest_validated"
	if handoff.Status == HandoffStatusValidated &&
		handoff.FromComponent == ComponentLabTrustGym &&
		handoff.ToComponent == ComponentProvabilityFabric {
		checks = append(checks, releasePassCheck(id, "HandoffManifest.v0 targets Provability Fabric with Validated status",
			map[string]any{"handoff_id": handoff.HandoffID, "handoff_kind": handoff.HandoffKind}))
	} else {
		checks = append(checks, releaseFailCheck(id, "HandoffManifest.v0 targets Provability Fabric with Validated status",
			ReasonHandoffInvalid, map[string]any{"status": handoff.Status}))
		failureCodes = append(failureCodes, ReasonHandoffInvalid)
	}
	if opts.AdmissionProfile != nil {
		kindID := "handoff_kind_matches_profile"
		allowed := opts.AdmissionProfile.RequiredHandoffKinds
		if len(allowed) == 0 {
			allowed = []string{"bundle_to_verifier"}
		}
		matched := false
		for _, kind := range allowed {
			if handoff.HandoffKind == kind {
				matched = true
				break
			}
		}
		if matched {
			checks = append(checks, releasePassCheck(kindID,
				"HandoffManifest handoff_kind matches admission profile",
				map[string]any{
					"handoff_kind":  handoff.HandoffKind,
					"handoff_id":    handoff.HandoffID,
					"profile_id":    opts.AdmissionProfile.ProfileID,
					"handoff_ref":   handoff.HandoffID,
				}))
		} else {
			checks = append(checks, releaseFailCheck(kindID,
				"HandoffManifest handoff_kind matches admission profile",
				FailureCodeReleaseModeHandoffKindMismatch,
				map[string]any{
					"expected":    allowed,
					"actual":      handoff.HandoffKind,
					"profile_id":  opts.AdmissionProfile.ProfileID,
					"handoff_ref": handoff.HandoffID,
				}))
			failureCodes = append(failureCodes, FailureCodeReleaseModeHandoffKindMismatch)
		}
	}
	return checks, failureCodes
}

func mapVerificationCheckToReleaseAdmission(c VerificationCheck) (ReleaseValidationCheck, []string) {
	var releaseID string
	switch c.CheckID {
	case "status_transition_policy":
		releaseID = "status_transition_validation"
	case "source_commit_not_placeholder":
		releaseID = "source_provenance_validation"
	case "signature_or_digest_present":
		releaseID = "signature_digest_validation"
	case "artifact_registry_admission":
		releaseID = "registry_admission_from_bundle"
	default:
		return ReleaseValidationCheck{}, nil
	}
	details := map[string]any{}
	for k, v := range c.Details {
		details[k] = v
	}
	if code, ok := c.Details["reason_code"].(string); ok {
		details["failure_code"] = code
	}
	if c.Status == CheckPassed {
		return releasePassCheck(releaseID, c.Description, details), nil
	}
	fc, _ := details["failure_code"].(string)
	if fc == "" {
		fc = ReasonRegistryAdmissionFailed
	}
	return releaseFailCheck(releaseID, c.Description, fc, details), []string{fc}
}
