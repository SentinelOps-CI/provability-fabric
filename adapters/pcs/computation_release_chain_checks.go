// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

const computationRepairHint = "Re-run the computation with the declared code commit and regenerate ComputationRunReceipt.v0 and ResultArtifact.v0."

// appendComputationReleaseChainChecks adds computation-specific RCVR checks with registry audit fields.
func appendComputationReleaseChainChecks(
	checks []ReleaseValidationCheck,
	failureCodes []string,
	bundle *ScienceClaimBundle,
	profile *AdmissionProfile,
) ([]ReleaseValidationCheck, []string) {
	if bundle == nil || profile == nil || !profile.IsComputationProfile() {
		return checks, failureCodes
	}
	specs := []struct {
		checkID      string
		registryRef  string
		artifactPath string
		eval         func(*ScienceClaimBundle) (ok bool, failureCode, expected, actual string)
	}{
		{
			checkID:      "computation_dataset_hash_consistent",
			registryRef:  "dataset_hash_matches_receipt",
			artifactPath: "dataset_receipt.json",
			eval:         evalComputationDatasetHash,
		},
		{
			checkID:      "computation_environment_hash_consistent",
			registryRef:  "environment_hash_matches_receipt",
			artifactPath: "environment_receipt.json",
			eval:         evalComputationEnvironmentHash,
		},
		{
			checkID:      "computation_result_hash_consistent",
			registryRef:  "result_hashes_match_result_artifacts",
			artifactPath: "result_artifact.json",
			eval:         evalComputationResultHash,
		},
		{
			checkID:      "computation_code_commit_present",
			registryRef:  "code_commit_present",
			artifactPath: "computation_run_receipt.json",
			eval:         evalComputationCodeCommit,
		},
		{
			checkID:      "computation_exit_code_zero",
			registryRef:  "run_receipt_hash_matches_declared_run",
			artifactPath: "computation_run_receipt.json",
			eval:         evalComputationExitCode,
		},
		{
			checkID:      "computation_witness_certificate_checked",
			registryRef:  "computation_status_checked_for_release",
			artifactPath: "computation_witness.json",
			eval:         evalComputationWitnessStatus,
		},
	}
	for _, spec := range specs {
		ok, fc, exp, act := spec.eval(bundle)
		c := computationReleaseCheck(spec.checkID, spec.registryRef, spec.artifactPath, ok, fc, exp, act)
		checks = append(checks, c)
		if !ok && fc != "" {
			failureCodes = append(failureCodes, fc)
		}
	}
	return checks, uniqueStrings(failureCodes)
}

func computationReleaseCheck(
	checkID, registryRef, artifactPath string,
	ok bool,
	failureCode, expected, actual string,
) ReleaseValidationCheck {
	details := map[string]any{
		"registry_check_ref":    registryRef,
		"artifact_path":         artifactPath,
		"responsible_component": ComponentScientificComputation,
		"repair_hint":           computationRepairHint,
	}
	refs := []string{registryRef}
	if ok {
		details["execution"] = RegistryExecutionPassed
		details["expected"] = expected
		details["actual"] = actual
		return ReleaseValidationCheck{
			CheckID: checkID, Description: checkID, Status: "passed", Details: details,
			RegistryCheckRefs: refs, ResponsibleComponent: ComponentScientificComputation,
		}
	}
	details["execution"] = RegistryExecutionFailed
	details["failure_code"] = failureCode
	details["expected"] = expected
	details["actual"] = actual
	return ReleaseValidationCheck{
		CheckID: checkID, Description: checkID, Status: "failed", Details: details,
		RegistryCheckRefs: refs, ResponsibleComponent: ComponentScientificComputation,
	}
}

func evalComputationDatasetHash(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.DatasetReceipt == nil || bundle.ComputationRunReceipt == nil {
		return false, FailureCodeMissingDatasetReceipt, "dataset_aggregate_hash aligned", "missing dataset or run receipt"
	}
	ds := bundle.DatasetReceipt.AggregateHash
	run := bundle.ComputationRunReceipt.DatasetAggregateHash
	if run == "" {
		run = ds
	}
	if run != ds {
		return false, FailureCodeDatasetHashMismatch, ds, run
	}
	return true, "", ds, run
}

func evalComputationEnvironmentHash(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.EnvironmentReceipt == nil || bundle.ComputationRunReceipt == nil {
		return false, FailureCodeMissingEnvironmentReceipt, "environment digest aligned", "missing environment or run receipt"
	}
	env := bundle.EnvironmentReceipt.Digest
	run := bundle.ComputationRunReceipt.EnvironmentDigest
	if run != env {
		return false, FailureCodeEnvironmentDigestMismatch, env, run
	}
	return true, "", env, run
}

func evalComputationResultHash(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.ResultArtifact == nil || bundle.ComputationWitness == nil {
		return false, FailureCodeMissingComputationWitness, "witness includes result hash", "missing result or witness"
	}
	h := bundle.ResultArtifact.ContentHash
	if !witnessResultHashesMatch(bundle.ComputationWitness.ResultHashes, h) {
		return false, FailureCodeResultHashMismatch, h, strings.Join(bundle.ComputationWitness.ResultHashes, ",")
	}
	return true, "", h, h
}

func evalComputationCodeCommit(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.ComputationRunReceipt == nil {
		return false, FailureCodeMissingComputationRunReceipt, "non-empty code_commit", "missing run receipt"
	}
	cc := strings.TrimSpace(bundle.ComputationRunReceipt.CodeCommit)
	if cc == "" || IsForbiddenPlaceholderCommit(cc) {
		return false, FailureCodeMissingCodeCommit, "valid git commit", cc
	}
	return true, "", "valid git commit", cc
}

func evalComputationExitCode(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.ComputationRunReceipt == nil {
		return false, FailureCodeMissingComputationRunReceipt, "exit_code=0", "missing run receipt"
	}
	code := bundle.ComputationRunReceipt.ExitCode
	if code != 0 {
		return false, FailureCodeNonzeroExitCode, "0", fmtInt(code)
	}
	return true, "", "0", "0"
}

func evalComputationWitnessStatus(bundle *ScienceClaimBundle) (bool, string, string, string) {
	if bundle.ComputationWitness == nil {
		return false, FailureCodeMissingComputationWitness, StatusCertificateChecked, "missing witness"
	}
	st := bundle.ComputationWitness.Status
	if st == StatusRejected {
		return false, FailureCodeRejectedComputationWitness, StatusCertificateChecked, st
	}
	if st != StatusCertificateChecked {
		return false, FailureCodeRejectedComputationWitness, StatusCertificateChecked, st
	}
	return true, "", StatusCertificateChecked, st
}

func fmtInt(n int) string {
	return fmt.Sprintf("%d", n)
}
