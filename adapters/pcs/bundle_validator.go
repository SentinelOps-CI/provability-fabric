// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"path/filepath"
	"strings"
)

// ValidateOptions configures bundle verification.
type ValidateOptions struct {
	RepoRoot          string
	VerifierVersion   string
	SourceCommit      string
	SkipSchemaValidate bool
}

// VerifyScienceClaimBundle runs all required v0.1 checks and returns VerificationResult.v0.
func VerifyScienceClaimBundle(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) (VerificationResult, error) {
	checks, err := runChecks(bundlePath, bundle, opts)
	if err != nil {
		return VerificationResult{}, err
	}
	result := BuildVerificationResult(bundle, checks, opts.VerifierVersion, opts.SourceCommit)
	if opts.RepoRoot != "" {
		if err := ValidateVerificationResult(opts.RepoRoot, result); err != nil {
			return VerificationResult{}, fmt.Errorf("verification result schema: %w", err)
		}
	}
	return result, nil
}

func runChecks(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) ([]VerificationCheck, error) {
	checks := []VerificationCheck{
		checkBundleSchema(bundlePath, bundle, opts),
		presenceCheck("pcs.presence.claim_artifact", "ClaimArtifact.v0 is present", bundle.ClaimArtifact != nil),
		presenceCheck("pcs.presence.assumption_set", "AssumptionSet.v0 is present", bundle.AssumptionSet != nil),
		presenceCheck("pcs.presence.runtime_receipt", "RuntimeReceipt.v0 is present", bundle.RuntimeReceipt != nil),
		presenceCheck("pcs.presence.trace_certificate", "TraceCertificate.v0 is present", bundle.TraceCertificate != nil),
		presenceCheck("pcs.presence.evidence_bundle", "EvidenceBundle.v0 is present", bundle.EvidenceBundle != nil),
		CheckAssumptionSetRefMatch(bundle.ClaimArtifact, bundle.AssumptionSet),
		CheckRuntimeTraceHashPresent(bundle.RuntimeReceipt),
		CheckTraceHashMatch(bundle.RuntimeReceipt, bundle.TraceCertificate),
		CheckCertificateStatus(bundle.TraceCertificate),
		checkEvidenceReferences(bundle),
		checkNotStale(bundle),
		checkMajorProvenance(bundle),
		checkMajorSignatures(bundle),
	}
	return NormalizeChecks(checks)
}

func checkBundleSchema(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) VerificationCheck {
	const id = "pcs.schema.science_claim_bundle"
	if opts.SkipSchemaValidate {
		return skipCheck(id, "ScienceClaimBundle.v0 schema is valid", "schema validation skipped")
	}
	repoRoot := opts.RepoRoot
	if repoRoot == "" {
		var err error
		repoRoot, err = FindRepoRoot(filepath.Dir(bundlePath))
		if err != nil {
			return failCheck(id, "ScienceClaimBundle.v0 schema is valid", err.Error())
		}
	}
	if err := ValidateScienceClaimBundleFile(repoRoot, bundlePath); err != nil {
		return failCheck(id, "ScienceClaimBundle.v0 schema is valid", err.Error())
	}
	if bundle != nil && bundle.SchemaVersion != "" && bundle.SchemaVersion != SchemaScienceClaimBundle {
		return failCheck(id, "ScienceClaimBundle.v0 schema is valid", "schema_version="+bundle.SchemaVersion)
	}
	return passCheck(id, "ScienceClaimBundle.v0 schema is valid", "config/schemas/pcs/ScienceClaimBundle.v0.schema.json")
}

func presenceCheck(id, description string, ok bool) VerificationCheck {
	if ok {
		return passCheck(id, description, "present")
	}
	return failCheck(id, description, "missing")
}

func checkEvidenceReferences(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "pcs.evidence.artifact_refs"
	ev := bundle.EvidenceBundle
	if ev == nil {
		return failCheck(id, "EvidenceBundle references included artifacts", "evidence bundle missing")
	}
	known := collectArtifactIDs(bundle)
	if len(ev.ArtifactRefs) == 0 {
		return failCheck(id, "EvidenceBundle references included artifacts", "artifact_refs is empty")
	}
	var missing []string
	for _, ref := range ev.ArtifactRefs {
		if _, ok := known[ref]; !ok {
			missing = append(missing, ref)
		}
	}
	if len(missing) > 0 {
		return failCheck(id, "EvidenceBundle references included artifacts", "unknown refs: "+strings.Join(missing, ", "))
	}
	return passCheck(id, "EvidenceBundle references included artifacts", strings.Join(ev.ArtifactRefs, ", "))
}

func collectArtifactIDs(bundle *ScienceClaimBundle) map[string]struct{} {
	ids := make(map[string]struct{})
	add := func(id string) {
		if id != "" {
			ids[id] = struct{}{}
		}
	}
	if bundle.ClaimArtifact != nil {
		add(bundle.ClaimArtifact.ArtifactID)
		add(bundle.ClaimArtifact.ClaimID)
		add(bundle.ClaimArtifact.AssumptionSetRef)
	}
	if bundle.AssumptionSet != nil {
		add(bundle.AssumptionSet.ArtifactID)
		add(bundle.AssumptionSet.AssumptionSetID)
	}
	if bundle.RuntimeReceipt != nil {
		add(bundle.RuntimeReceipt.ArtifactID)
		add(bundle.RuntimeReceipt.ReceiptID)
	}
	if bundle.TraceCertificate != nil {
		add(bundle.TraceCertificate.ArtifactID)
		add(bundle.TraceCertificate.CertificateID)
	}
	if bundle.EvidenceBundle != nil {
		add(bundle.EvidenceBundle.ArtifactID)
		add(bundle.EvidenceBundle.EvidenceBundleID)
	}
	return ids
}

func checkNotStale(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "pcs.artifact.not_stale"
	names := []string{"claim_artifact", "assumption_set", "runtime_receipt", "trace_certificate", "evidence_bundle"}
	metas := []*MajorArtifactMeta{
		artifactMetaClaim(bundle.ClaimArtifact),
		artifactMetaAssumption(bundle.AssumptionSet),
		artifactMetaReceipt(bundle.RuntimeReceipt),
		artifactMetaCert(bundle.TraceCertificate),
		artifactMetaEvidence(bundle.EvidenceBundle),
	}
	var stale []string
	for i, meta := range metas {
		if meta == nil {
			continue
		}
		if meta.Status == StatusStale {
			stale = append(stale, names[i])
		}
	}
	if len(stale) > 0 {
		return failCheck(id, "No required artifact has status Stale", strings.Join(stale, ", "))
	}
	return passCheck(id, "No required artifact has status Stale", "ok")
}

func checkMajorProvenance(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "pcs.metadata.source_provenance"
	var missing []string
	for name, meta := range majorArtifacts(bundle) {
		if meta == nil {
			missing = append(missing, name+"(missing)")
			continue
		}
		if strings.TrimSpace(meta.SourceRepo) == "" || strings.TrimSpace(meta.SourceCommit) == "" {
			missing = append(missing, name)
		}
	}
	if len(missing) > 0 {
		return failCheck(id, "source_repo and source_commit are present for all major artifacts", strings.Join(missing, ", "))
	}
	return passCheck(id, "source_repo and source_commit are present for all major artifacts", "ok")
}

func checkMajorSignatures(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "pcs.metadata.signature_or_digest"
	var missing []string
	for name, meta := range majorArtifacts(bundle) {
		if meta == nil {
			missing = append(missing, name+"(missing)")
			continue
		}
		if strings.TrimSpace(meta.SignatureOrDigest) == "" {
			missing = append(missing, name)
		}
	}
	if len(missing) > 0 {
		return failCheck(id, "signature_or_digest is present for all major artifacts", strings.Join(missing, ", "))
	}
	return passCheck(id, "signature_or_digest is present for all major artifacts", "ok")
}

func majorArtifacts(bundle *ScienceClaimBundle) map[string]*MajorArtifactMeta {
	return map[string]*MajorArtifactMeta{
		"claim_artifact":    artifactMetaClaim(bundle.ClaimArtifact),
		"assumption_set":    artifactMetaAssumption(bundle.AssumptionSet),
		"runtime_receipt":   artifactMetaReceipt(bundle.RuntimeReceipt),
		"trace_certificate": artifactMetaCert(bundle.TraceCertificate),
		"evidence_bundle":   artifactMetaEvidence(bundle.EvidenceBundle),
	}
}

func artifactMetaClaim(c *ClaimArtifact) *MajorArtifactMeta {
	if c == nil {
		return nil
	}
	m := c.MajorArtifactMeta
	return &m
}

func artifactMetaAssumption(a *AssumptionSet) *MajorArtifactMeta {
	if a == nil {
		return nil
	}
	m := a.MajorArtifactMeta
	return &m
}

func artifactMetaReceipt(r *RuntimeReceipt) *MajorArtifactMeta {
	if r == nil {
		return nil
	}
	m := r.MajorArtifactMeta
	return &m
}

func artifactMetaCert(c *TraceCertificate) *MajorArtifactMeta {
	if c == nil {
		return nil
	}
	m := c.MajorArtifactMeta
	return &m
}

func artifactMetaEvidence(e *EvidenceBundle) *MajorArtifactMeta {
	if e == nil {
		return nil
	}
	m := e.MajorArtifactMeta
	return &m
}

