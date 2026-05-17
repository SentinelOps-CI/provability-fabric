// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// Canonical PCS status values used in v0.1 verification.
const (
	StatusCertificateChecked = "CertificateChecked"
	StatusRejected           = "Rejected"
	StatusStale              = "Stale"

	// ZeroSourceCommitPlaceholder is rejected in release mode (unless local_dev).
	ZeroSourceCommitPlaceholder = "0000000000000000000000000000000000000000"
)

// MajorArtifactMeta is shared provenance metadata required on major artifacts.
type MajorArtifactMeta struct {
	SchemaVersion     string `json:"schema_version"`
	CreatedAt         string `json:"created_at"`
	Producer          string `json:"producer"`
	ProducerVersion   string `json:"producer_version"`
	SourceRepo        string `json:"source_repo"`
	SourceCommit      string `json:"source_commit"`
	Status            string `json:"status"`
	SignatureOrDigest string `json:"signature_or_digest"`
	ArtifactID        string `json:"artifact_id,omitempty"`
}

// ScienceClaimBundle is the PCS ScienceClaimBundle.v0 envelope from LabTrust.
type ScienceClaimBundle struct {
	SchemaVersion     string              `json:"schema_version"`
	BundleID          string              `json:"bundle_id"`
	CreatedAt         string              `json:"created_at"`
	Producer          string              `json:"producer"`
	ProducerVersion   string              `json:"producer_version"`
	SourceRepo        string              `json:"source_repo"`
	SourceCommit      string              `json:"source_commit"`
	Status            string              `json:"status"`
	SignatureOrDigest string              `json:"signature_or_digest"`
	LocalDev          bool                `json:"local_dev,omitempty"`
	ClaimArtifact     *ClaimArtifact      `json:"claim_artifact"`
	AssumptionSet     *AssumptionSet      `json:"assumption_set"`
	RuntimeReceipt    *RuntimeReceipt     `json:"runtime_receipt"`
	TraceCertificate  *TraceCertificate   `json:"trace_certificate,omitempty"`
	TraceCertificates []*TraceCertificate `json:"trace_certificates,omitempty"`
	EvidenceBundle    *EvidenceBundle     `json:"evidence_bundle"`
}

// TraceCertificatesList returns one or more trace certificates from the bundle.
func (b *ScienceClaimBundle) TraceCertificatesList() []*TraceCertificate {
	if b == nil {
		return nil
	}
	if len(b.TraceCertificates) > 0 {
		return b.TraceCertificates
	}
	if b.TraceCertificate != nil {
		return []*TraceCertificate{b.TraceCertificate}
	}
	return nil
}

type ClaimArtifact struct {
	MajorArtifactMeta
	ClaimID          string `json:"claim_id"`
	AssumptionSetRef string `json:"assumption_set_ref"`
}

type AssumptionSet struct {
	MajorArtifactMeta
	AssumptionSetID string `json:"assumption_set_id"`
}

type RuntimeReceipt struct {
	MajorArtifactMeta
	ReceiptID string `json:"receipt_id"`
	TraceHash string `json:"trace_hash"`
}

type TraceCertificate struct {
	MajorArtifactMeta
	CertificateID string `json:"certificate_id"`
	TraceHash     string `json:"trace_hash"`
}

type EvidenceBundle struct {
	MajorArtifactMeta
	EvidenceBundleID string   `json:"evidence_bundle_id"`
	ArtifactRefs     []string `json:"artifact_refs"`
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
	SignatureOrDigest  string              `json:"signature_or_digest"`
}

const (
	VerifierName           = "Provability Fabric"
	VerifierSourceRepo     = "https://github.com/SentinelOps-CI/provability-fabric"
	SchemaVersionV0        = "v0"
	SchemaScienceClaimBundle = "ScienceClaimBundle.v0"
	DefaultVerifierVersion = "0.1.0"
)
