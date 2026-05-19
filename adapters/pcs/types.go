// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// Canonical PCS status values used in v0.1 verification.
const (
	StatusCertificateChecked = "CertificateChecked"
	StatusProofChecked       = "ProofChecked"
	StatusRuntimeObserved    = "RuntimeObserved"
	StatusRejected           = "Rejected"
	StatusStale              = "Stale"

	// ZeroSourceCommitPlaceholder is rejected in release mode (unless local_dev).
	ZeroSourceCommitPlaceholder = "0000000000000000000000000000000000000000"
)

// ScienceClaimBundle is the pcs-core canonical ScienceClaimBundle.v0 envelope.
type ScienceClaimBundle struct {
	BundleID            string               `json:"bundle_id"`
	SchemaVersion       string               `json:"schema_version"`
	WorkflowID          string               `json:"workflow_id,omitempty"`
	ToolUseTrace           *ToolUseTraceV0           `json:"tool_use_trace,omitempty"`
	ToolUseCertificate     *ToolUseCertificateV0     `json:"tool_use_certificate,omitempty"`
	DatasetReceipt         *DatasetReceiptV0         `json:"dataset_receipt,omitempty"`
	EnvironmentReceipt     *EnvironmentReceiptV0     `json:"environment_receipt,omitempty"`
	ComputationRunReceipt  *ComputationRunReceiptV0  `json:"computation_run_receipt,omitempty"`
	ResultArtifact         *ResultArtifactV0         `json:"result_artifact,omitempty"`
	ComputationWitness     *ComputationWitnessV0     `json:"computation_witness,omitempty"`
	ClaimArtifact          *ClaimArtifact            `json:"claim_artifact"`
	AssumptionSet       *AssumptionSet       `json:"assumption_set"`
	RuntimeReceipts     []*RuntimeReceipt    `json:"runtime_receipts"`
	Certificates        []*TraceCertificate  `json:"certificates"`
	EvidenceBundle      *EvidenceBundle      `json:"evidence_bundle"`
	VerificationPolicy  *VerificationPolicy  `json:"verification_policy"`
	CreatedAt           string               `json:"created_at"`
	Producer            string               `json:"producer"`
	ProducerVersion     string               `json:"producer_version"`
	SourceRepo          string               `json:"source_repo"`
	SourceCommit        string               `json:"source_commit"`
	SignatureOrDigest   string               `json:"signature_or_digest"`
	LocalDev            bool                 `json:"local_dev,omitempty"`
}

// PrimaryRuntimeReceipt returns the first runtime receipt (v0.1 expects exactly one).
func (b *ScienceClaimBundle) PrimaryRuntimeReceipt() *RuntimeReceipt {
	if b == nil || len(b.RuntimeReceipts) == 0 {
		return nil
	}
	return b.RuntimeReceipts[0]
}

type VerificationPolicy struct {
	PolicyID        string   `json:"policy_id"`
	RequiredChecks  []string `json:"required_checks"`
}

type ClaimArtifact struct {
	ArtifactID          string   `json:"artifact_id"`
	ArtifactType        string   `json:"artifact_type"`
	SchemaVersion       string   `json:"schema_version"`
	ClaimText           string   `json:"claim_text"`
	ClaimKind           string   `json:"claim_kind"`
	Status              string   `json:"status"`
	AssumptionSetRef    string   `json:"assumption_set_ref"`
	SourceSpanRefs      []string `json:"source_span_refs"`
	FormalStatement     string   `json:"formal_statement"`
	CertificateRefs     []string `json:"certificate_refs"`
	RuntimeReceiptRefs  []string `json:"runtime_receipt_refs"`
	CreatedAt           string   `json:"created_at"`
	Producer            string   `json:"producer"`
	ProducerVersion     string   `json:"producer_version"`
	SourceRepo          string   `json:"source_repo"`
	SourceCommit        string   `json:"source_commit"`
	SignatureOrDigest   string   `json:"signature_or_digest"`
}

type Assumption struct {
	AssumptionID    string   `json:"assumption_id"`
	Text            string   `json:"text"`
	Kind            string   `json:"kind"`
	Status          string   `json:"status"`
	SourceSpanRefs  []string `json:"source_span_refs"`
}

type AssumptionSet struct {
	AssumptionSetID     string       `json:"assumption_set_id"`
	SchemaVersion       string       `json:"schema_version"`
	CreatedAt           string       `json:"created_at"`
	Producer            string       `json:"producer"`
	ProducerVersion     string       `json:"producer_version"`
	SourceRepo          string       `json:"source_repo"`
	SourceCommit        string       `json:"source_commit"`
	Assumptions         []Assumption `json:"assumptions"`
	HumanReviewStatus   string       `json:"human_review_status"`
	Status              string       `json:"status"`
	SignatureOrDigest   string       `json:"signature_or_digest"`
}

type RuntimeReceipt struct {
	ReceiptID         string            `json:"receipt_id"`
	SchemaVersion     string            `json:"schema_version"`
	RunID             string            `json:"run_id"`
	Environment       map[string]string `json:"environment"`
	StartedAt         string            `json:"started_at"`
	EndedAt           string            `json:"ended_at"`
	Status            string            `json:"status"`
	RunOutcome        string            `json:"run_outcome"`
	FinalReasonCode   string            `json:"final_reason_code"`
	Released          bool              `json:"released"`
	EventsHash        string            `json:"events_hash"`
	PolicyHash        string            `json:"policy_hash"`
	TraceHash         string            `json:"trace_hash"`
	Producer          string            `json:"producer"`
	ProducerVersion   string            `json:"producer_version"`
	SourceRepo        string            `json:"source_repo"`
	SourceCommit      string            `json:"source_commit"`
	LocalDev          bool              `json:"local_dev,omitempty"`
	InputHashes       map[string]string `json:"input_hashes"`
	OutputHashes      map[string]string `json:"output_hashes"`
	SignatureOrDigest string            `json:"signature_or_digest"`
}

type TraceCertificate struct {
	CertificateID     string  `json:"certificate_id"`
	SchemaVersion     string  `json:"schema_version"`
	TraceHash         string  `json:"trace_hash"`
	SpecHash          string  `json:"spec_hash"`
	PropertyID        string  `json:"property_id"`
	Checker           string  `json:"checker"`
	CheckerVersion    string  `json:"checker_version"`
	Status            string  `json:"status"`
	CounterexampleRef *string `json:"counterexample_ref"`
	CreatedAt         string  `json:"created_at"`
	Producer          string  `json:"producer"`
	ProducerVersion   string  `json:"producer_version"`
	SourceRepo        string  `json:"source_repo"`
	SourceCommit      string  `json:"source_commit"`
	SignatureOrDigest string  `json:"signature_or_digest"`
}

type EvidenceBundle struct {
	BundleID            string            `json:"bundle_id"`
	SchemaVersion       string            `json:"schema_version"`
	ClaimRefs           []string          `json:"claim_refs"`
	AssumptionSetRefs   []string          `json:"assumption_set_refs"`
	RuntimeReceiptRefs  []string          `json:"runtime_receipt_refs"`
	CertificateRefs     []string          `json:"certificate_refs"`
	ArtifactHashes      map[string]string `json:"artifact_hashes"`
	CreatedAt           string            `json:"created_at"`
	Producer            string            `json:"producer"`
	ProducerVersion     string            `json:"producer_version"`
	SourceRepo          string            `json:"source_repo"`
	SourceCommit        string            `json:"source_commit"`
	SignatureOrDigest   string            `json:"signature_or_digest"`
}

// ArtifactProvenance is shared provenance metadata for verification checks.
type ArtifactProvenance struct {
	SourceRepo        string
	SourceCommit      string
	Status            string
	SignatureOrDigest string
}

// CheckStatus is a single verification check outcome.
type CheckStatus string

const (
	CheckPassed  CheckStatus = "passed"
	CheckFailed  CheckStatus = "failed"
	CheckSkipped CheckStatus = "skipped"
	CheckWarning CheckStatus = "warning"
)

// VerificationCheck is one row in VerificationResult.checks.
type VerificationCheck struct {
	CheckID     string         `json:"check_id"`
	Description string         `json:"description"`
	Status      CheckStatus    `json:"status"`
	Details     map[string]any `json:"details"`
}

// VerificationResult is emitted by Provability Fabric (schema_version v0).
type VerificationResult struct {
	SchemaVersion     string              `json:"schema_version"`
	VerificationID    string              `json:"verification_id"`
	BundleID          string              `json:"bundle_id"`
	Verifier          string              `json:"verifier"`
	VerifierVersion   string              `json:"verifier_version"`
	Status            string              `json:"status"`
	Checks            []VerificationCheck `json:"checks"`
	CreatedAt         string              `json:"created_at"`
	SourceRepo        string              `json:"source_repo"`
	SourceCommit      string              `json:"source_commit"`
	SignatureOrDigest string              `json:"signature_or_digest"`
	VerifiedInput     *VerifiedInput      `json:"verified_input,omitempty"`
}

// SignedScienceClaimBundle is the importable signed wrapper for Scientific Memory.
type SignedScienceClaimBundle struct {
	SchemaVersion      string              `json:"schema_version"`
	SignedBundleID     string              `json:"signed_bundle_id"`
	ScienceClaimBundle *ScienceClaimBundle `json:"science_claim_bundle"`
	VerificationResult VerificationResult  `json:"verification_result"`
	Signer             string              `json:"signer"`
	SignedAt           string              `json:"signed_at"`
	SourceRepo         string              `json:"source_repo"`
	SourceCommit       string              `json:"source_commit"`
	SignatureOrDigest     string              `json:"signature_or_digest"`
	SignedInputBundleHash string              `json:"signed_input_bundle_hash,omitempty"`
	LocalDev              bool                `json:"local_dev,omitempty"`
}

const (
	VerifierName           = "Provability Fabric"
	VerifierSourceRepo     = "https://github.com/SentinelOps-CI/provability-fabric"
	SchemaVersionV0        = "v0"
	DefaultVerifierVersion = "0.1.0"
)
