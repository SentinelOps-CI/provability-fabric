// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

const workflowScientificComputationRepro = "scientific_computation.reproducibility_v0"
const ComponentScientificComputation = "ScientificComputation"

// DatasetReceiptV0 records dataset provenance for a computation release.
type DatasetReceiptV0 struct {
	SchemaVersion     string `json:"schema_version"`
	ReceiptID         string `json:"receipt_id"`
	DatasetID         string `json:"dataset_id,omitempty"`
	AggregateHash     string `json:"aggregate_hash"`
	Producer          string `json:"producer,omitempty"`
	SignatureOrDigest string `json:"signature_or_digest,omitempty"`
}

// EnvironmentReceiptV0 records the execution environment digest.
type EnvironmentReceiptV0 struct {
	SchemaVersion     string `json:"schema_version"`
	ReceiptID         string `json:"receipt_id,omitempty"`
	EnvironmentID     string `json:"environment_id,omitempty"`
	Digest            string `json:"digest"`
	Producer          string `json:"producer,omitempty"`
	SignatureOrDigest string `json:"signature_or_digest,omitempty"`
}

// ComputationRunReceiptV0 records a single computation run.
type ComputationRunReceiptV0 struct {
	SchemaVersion        string `json:"schema_version"`
	RunID                string `json:"run_id"`
	CodeCommit           string `json:"code_commit"`
	ExitCode             int    `json:"exit_code"`
	DatasetAggregateHash string `json:"dataset_aggregate_hash"`
	EnvironmentDigest    string `json:"environment_digest"`
	Producer             string `json:"producer,omitempty"`
	SignatureOrDigest    string `json:"signature_or_digest,omitempty"`
}

// ResultArtifactV0 is the primary output of a computation run.
type ResultArtifactV0 struct {
	SchemaVersion     string `json:"schema_version"`
	ArtifactID        string `json:"artifact_id"`
	ResultID          string `json:"result_id,omitempty"`
	ContentHash       string `json:"content_hash"`
	SHA256            string `json:"sha256,omitempty"`
	Producer          string `json:"producer,omitempty"`
	SignatureOrDigest string `json:"signature_or_digest,omitempty"`
}

// ComputationWitnessV0 certifies computation reproducibility claims.
type ComputationWitnessV0 struct {
	SchemaVersion        string   `json:"schema_version"`
	CertificateID        string   `json:"certificate_id"`
	WitnessID            string   `json:"witness_id,omitempty"`
	Status               string   `json:"status"`
	ResultHashes         []string `json:"result_hashes"`
	DatasetAggregateHash string   `json:"dataset_aggregate_hash,omitempty"`
	DatasetHash          string   `json:"dataset_hash,omitempty"`
	EnvironmentDigest    string   `json:"environment_digest,omitempty"`
	EnvironmentHash      string   `json:"environment_hash,omitempty"`
	Producer             string   `json:"producer,omitempty"`
	SignatureOrDigest    string   `json:"signature_or_digest,omitempty"`
}

// IsComputationProfile reports whether this profile targets scientific computation reproducibility.
func (p *AdmissionProfile) IsComputationProfile() bool {
	if p == nil {
		return false
	}
	p.normalize()
	return strings.HasPrefix(p.WorkflowID, "scientific_computation")
}

func inferComputationWorkflow(bundle *ScienceClaimBundle) bool {
	if bundle == nil {
		return false
	}
	if strings.TrimSpace(bundle.WorkflowID) == workflowScientificComputationRepro {
		return true
	}
	if bundle.VerificationPolicy != nil &&
		strings.TrimSpace(bundle.VerificationPolicy.PolicyID) == workflowScientificComputationRepro {
		return true
	}
	return bundle.DatasetReceipt != nil ||
		bundle.EnvironmentReceipt != nil ||
		bundle.ComputationRunReceipt != nil ||
		bundle.ResultArtifact != nil ||
		bundle.ComputationWitness != nil
}

func enforceScientificComputationProfile(profile *AdmissionProfile, bundle *ScienceClaimBundle, handoff *LoadedHandoff) error {
	if bundle == nil {
		return fmt.Errorf("%s: profile %q requires a science claim bundle", FailureCodeReleaseModeBundleRequired, profile.ProfileID)
	}
	if bundle.ToolUseTrace != nil || bundle.ToolUseCertificate != nil {
		return fmt.Errorf("%s: bundle %q is agent tool-use workflow %q, profile %q expects %q",
			FailureCodeAdmissionProfileWorkflowMismatch, bundle.BundleID, InferBundleWorkflowID(bundle), profile.ProfileID, profile.WorkflowID)
	}
	if bundle.ClaimArtifact != nil && !isComputationReleaseBundle(bundle) {
		return fmt.Errorf("%s: bundle %q is labtrust workflow %q, profile %q expects %q",
			FailureCodeAdmissionProfileWorkflowMismatch, bundle.BundleID, InferBundleWorkflowID(bundle), profile.ProfileID, profile.WorkflowID)
	}
	NormalizeComputationBundle(bundle)
	if err := validateAdmissionProfileWorkflow(profile, bundle); err != nil {
		return err
	}
	if err := enforceProfileHandoff(profile, handoff); err != nil {
		return err
	}
	if bundle.DatasetReceipt == nil {
		return fmt.Errorf("%s: missing DatasetReceipt.v0", FailureCodeMissingDatasetReceipt)
	}
	if strings.TrimSpace(bundle.DatasetReceipt.AggregateHash) == "" {
		return fmt.Errorf("%s: DatasetReceipt.v0.aggregate_hash is empty", FailureCodeMissingDatasetReceipt)
	}
	if bundle.EnvironmentReceipt == nil {
		return fmt.Errorf("%s: missing EnvironmentReceipt.v0", FailureCodeMissingEnvironmentReceipt)
	}
	if strings.TrimSpace(bundle.EnvironmentReceipt.Digest) == "" {
		return fmt.Errorf("%s: EnvironmentReceipt.v0.digest is empty", FailureCodeMissingEnvironmentReceipt)
	}
	if bundle.ComputationRunReceipt == nil {
		return fmt.Errorf("%s: missing ComputationRunReceipt.v0", FailureCodeMissingComputationRunReceipt)
	}
	run := bundle.ComputationRunReceipt
	if strings.TrimSpace(run.CodeCommit) == "" {
		return fmt.Errorf("%s: ComputationRunReceipt.v0.code_commit is empty", FailureCodeMissingCodeCommit)
	}
	if IsForbiddenPlaceholderCommit(run.CodeCommit) {
		return fmt.Errorf("%s: ComputationRunReceipt.v0.code_commit is a placeholder", FailureCodeMissingCodeCommit)
	}
	if run.ExitCode != 0 {
		return fmt.Errorf("%s: ComputationRunReceipt.v0.exit_code=%d", FailureCodeNonzeroExitCode, run.ExitCode)
	}
	if bundle.ResultArtifact == nil {
		return fmt.Errorf("%s: missing ResultArtifact.v0", FailureCodeAdmissionProfileRequiredArtifactMissing)
	}
	if strings.TrimSpace(bundle.ResultArtifact.ContentHash) == "" {
		return fmt.Errorf("%s: ResultArtifact.v0.content_hash is empty", FailureCodeAdmissionProfileRequiredArtifactMissing)
	}
	if bundle.ComputationWitness == nil {
		return fmt.Errorf("%s: missing ComputationWitness.v0", FailureCodeMissingComputationWitness)
	}
	witness := bundle.ComputationWitness
	if witness.Status == StatusRejected {
		return fmt.Errorf("%s: ComputationWitness.v0 status is Rejected", FailureCodeRejectedComputationWitness)
	}
	if witness.Status != StatusCertificateChecked {
		return fmt.Errorf("%s: ComputationWitness.v0 status %q (expected %q)",
			FailureCodeRejectedComputationWitness, witness.Status, StatusCertificateChecked)
	}
	if err := validateComputationHashes(bundle); err != nil {
		return err
	}
	return nil
}

func validateComputationHashes(bundle *ScienceClaimBundle) error {
	ds := bundle.DatasetReceipt.AggregateHash
	env := bundle.EnvironmentReceipt.Digest
	run := bundle.ComputationRunReceipt
	resultHash := bundle.ResultArtifact.ContentHash
	witness := bundle.ComputationWitness

	if run.DatasetAggregateHash != "" && run.DatasetAggregateHash != ds {
		return fmt.Errorf("%s: run dataset_aggregate_hash %s != dataset receipt %s",
			FailureCodeDatasetHashMismatch, run.DatasetAggregateHash, ds)
	}
	if witness.DatasetAggregateHash != "" && witness.DatasetAggregateHash != ds {
		return fmt.Errorf("%s: witness dataset_aggregate_hash %s != dataset receipt %s",
			FailureCodeDatasetHashMismatch, witness.DatasetAggregateHash, ds)
	}
	if run.EnvironmentDigest != "" && run.EnvironmentDigest != env {
		return fmt.Errorf("%s: run environment_digest %s != environment receipt %s",
			FailureCodeEnvironmentDigestMismatch, run.EnvironmentDigest, env)
	}
	if witness.EnvironmentDigest != "" && witness.EnvironmentDigest != env {
		return fmt.Errorf("%s: witness environment_digest %s != environment receipt %s",
			FailureCodeEnvironmentDigestMismatch, witness.EnvironmentDigest, env)
	}
	if !witnessResultHashesMatch(witness.ResultHashes, resultHash) {
		return fmt.Errorf("%s: ComputationWitness.v0.result_hashes do not include ResultArtifact.v0.content_hash %s",
			FailureCodeResultHashMismatch, resultHash)
	}
	return nil
}

func witnessResultHashesMatch(hashes []string, contentHash string) bool {
	for _, h := range hashes {
		if h == contentHash {
			return true
		}
	}
	return false
}

// ValidateComputationBundleAdmission runs profile admission rules and returns the first failure code.
func ValidateComputationBundleAdmission(bundle *ScienceClaimBundle, profile *AdmissionProfile, handoff *LoadedHandoff) string {
	if err := enforceScientificComputationProfile(profile, bundle, handoff); err != nil {
		return extractFailureCode(err.Error())
	}
	return ""
}

func extractFailureCode(msg string) string {
	if idx := strings.Index(msg, ":"); idx > 0 {
		code := strings.TrimSpace(msg[:idx])
		if strings.Contains(code, "_") {
			return code
		}
	}
	return msg
}

// BuildComputationVerificationResult emits ProofChecked when computation admission passes.
func BuildComputationVerificationResult(bundle *ScienceClaimBundle, opts ValidateOptions) VerificationResult {
	checks := []VerificationCheck{
		{CheckID: "computation_artifacts_present", Status: CheckPassed, Description: "Computation artifacts present in bundle"},
		{CheckID: "computation_witness_checked", Status: CheckPassed, Description: "ComputationWitness.v0 status is CertificateChecked"},
	}
	result := BuildVerificationResult(bundle, checks, opts.VerifierVersion, opts.SourceCommit)
	result.Status = StatusProofChecked
	return result
}
