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
	RepoRoot           string
	VerifierVersion    string
	SourceCommit       string
	LocalDev           bool
	SkipSchemaValidate bool
}

// VerifyScienceClaimBundle runs all required v0.1 checks and returns VerificationResult.
func VerifyScienceClaimBundle(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) (VerificationResult, error) {
	if bundle != nil && bundle.LocalDev {
		opts.LocalDev = true
	}
	checks, err := runChecks(bundlePath, bundle, opts)
	if err != nil {
		return VerificationResult{}, err
	}
	result := BuildVerificationResult(bundle, checks, opts.VerifierVersion, opts.SourceCommit)
	if err := ValidateVerificationResult(opts.RepoRoot, result); err != nil {
		return VerificationResult{}, fmt.Errorf("verification result schema: %w", err)
	}
	return result, nil
}

func runChecks(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) ([]VerificationCheck, error) {
	certs := bundle.TraceCertificatesList()

	checks := []VerificationCheck{
		checkBundleSchema(bundlePath, bundle, opts),
		presenceCheck("claim_artifact_present", "ClaimArtifact.v0 exists", "claim_artifact", bundle.ClaimArtifact != nil),
		presenceCheck("assumption_set_present", "AssumptionSet.v0 exists", "assumption_set", bundle.AssumptionSet != nil),
		presenceCheck("runtime_receipt_present", "RuntimeReceipt.v0 exists", "runtime_receipt", bundle.RuntimeReceipt != nil),
		presenceCheck("trace_certificate_present", "At least one TraceCertificate.v0 exists", "trace_certificate", len(certs) > 0),
		presenceCheck("evidence_bundle_present", "EvidenceBundle.v0 exists", "evidence_bundle", bundle.EvidenceBundle != nil),
		CheckAssumptionSetRefMatch(bundle.ClaimArtifact, bundle.AssumptionSet),
		CheckRuntimeTraceHashPresent(bundle.RuntimeReceipt),
		CheckAllTraceHashAlignment(bundle.RuntimeReceipt, certs),
		CheckAllCertificateStatus(certs),
		checkEvidenceRefsComplete(bundle),
		checkNotStale(bundle),
		checkSourceProvenance(bundle),
		checkSignaturesPresent(bundle),
		checkSourceCommitNotPlaceholder(bundle, opts.LocalDev),
	}
	return NormalizeChecks(checks)
}

func checkBundleSchema(bundlePath string, bundle *ScienceClaimBundle, opts ValidateOptions) VerificationCheck {
	const id = "science_claim_bundle_schema"
	if opts.SkipSchemaValidate {
		return skipCheck(id, "ScienceClaimBundle.v0 schema is valid", detailMsg("schema validation skipped"))
	}
	repoRoot := opts.RepoRoot
	if repoRoot == "" {
		repoRoot, _ = FindRepoRoot(filepath.Dir(bundlePath))
	}
	if err := ValidateScienceClaimBundleFile(repoRoot, bundlePath); err != nil {
		return failCheck(id, "ScienceClaimBundle.v0 schema is valid", ReasonSchemaInvalid, detailMsg(err.Error()))
	}
	if bundle != nil && bundle.SchemaVersion != "" && bundle.SchemaVersion != SchemaScienceClaimBundle {
		return failCheck(id, "ScienceClaimBundle.v0 schema is valid", ReasonSchemaInvalid,
			map[string]any{"schema_version": bundle.SchemaVersion})
	}
	return passCheck(id, "ScienceClaimBundle.v0 schema is valid",
		map[string]any{"schema": "config/schemas/pcs/ScienceClaimBundle.v0.schema.json"})
}

func presenceCheck(id, description, artifact string, ok bool) VerificationCheck {
	if ok {
		return passCheck(id, description, map[string]any{"present": true, "artifact": artifact})
	}
	return failCheck(id, description, ReasonArtifactMissing, map[string]any{"present": false, "artifact": artifact})
}

func checkEvidenceRefsComplete(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "evidence_refs_complete"
	ev := bundle.EvidenceBundle
	if ev == nil {
		return failCheck(id, "EvidenceBundle references claim, assumption set, receipt, and certificate",
			ReasonEvidenceRefsIncomplete, detailMsg("evidence bundle missing"))
	}
	required := requiredEvidenceRefIDs(bundle)
	if len(required) < 4 {
		return failCheck(id, "EvidenceBundle references claim, assumption set, receipt, and certificate",
			ReasonEvidenceRefsIncomplete, map[string]any{"required_refs": required, "message": "missing component artifacts"})
	}
	refSet := make(map[string]struct{}, len(ev.ArtifactRefs))
	for _, ref := range ev.ArtifactRefs {
		refSet[ref] = struct{}{}
	}
	var missing []string
	for _, req := range required {
		if _, ok := refSet[req]; !ok {
			missing = append(missing, req)
		}
	}
	if len(missing) > 0 {
		return failCheck(id, "EvidenceBundle references claim, assumption set, receipt, and certificate",
			ReasonEvidenceRefsIncomplete, map[string]any{"missing_refs": missing, "artifact_refs": ev.ArtifactRefs})
	}
	return passCheck(id, "EvidenceBundle references claim, assumption set, receipt, and certificate",
		map[string]any{"artifact_refs": ev.ArtifactRefs})
}

func requiredEvidenceRefIDs(bundle *ScienceClaimBundle) []string {
	var refs []string
	if bundle.ClaimArtifact != nil {
		if id := bundle.ClaimArtifact.ClaimID; id != "" {
			refs = append(refs, id)
		} else if id := bundle.ClaimArtifact.ArtifactID; id != "" {
			refs = append(refs, id)
		}
	}
	if bundle.AssumptionSet != nil {
		if id := bundle.AssumptionSet.AssumptionSetID; id != "" {
			refs = append(refs, id)
		} else if id := bundle.AssumptionSet.ArtifactID; id != "" {
			refs = append(refs, id)
		}
	}
	if bundle.RuntimeReceipt != nil {
		if id := bundle.RuntimeReceipt.ReceiptID; id != "" {
			refs = append(refs, id)
		} else if id := bundle.RuntimeReceipt.ArtifactID; id != "" {
			refs = append(refs, id)
		}
	}
	for _, cert := range bundle.TraceCertificatesList() {
		if cert == nil {
			continue
		}
		if id := cert.CertificateID; id != "" {
			refs = append(refs, id)
			break
		}
		if id := cert.ArtifactID; id != "" {
			refs = append(refs, id)
			break
		}
	}
	return refs
}

func checkNotStale(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "artifact_not_stale"
	names := []string{"claim_artifact", "assumption_set", "runtime_receipt", "trace_certificate", "evidence_bundle"}
	var certMeta *MajorArtifactMeta
	if certs := bundle.TraceCertificatesList(); len(certs) > 0 {
		certMeta = artifactMetaCert(certs[0])
	}
	metas := []*MajorArtifactMeta{
		artifactMetaClaim(bundle.ClaimArtifact),
		artifactMetaAssumption(bundle.AssumptionSet),
		artifactMetaReceipt(bundle.RuntimeReceipt),
		certMeta,
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
		return failCheck(id, "No required artifact has status Stale", ReasonArtifactStale, map[string]any{"stale_artifacts": stale})
	}
	return passCheck(id, "No required artifact has status Stale", map[string]any{})
}

func checkSourceProvenance(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "source_provenance_present"
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
	if strings.TrimSpace(bundle.SourceRepo) == "" || strings.TrimSpace(bundle.SourceCommit) == "" {
		missing = append(missing, "bundle")
	}
	if len(missing) > 0 {
		return failCheck(id, "source_repo and source_commit are present", ReasonSourceProvenanceMissing, map[string]any{"missing": missing})
	}
	return passCheck(id, "source_repo and source_commit are present", map[string]any{})
}

func checkSignaturesPresent(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "signature_or_digest_present"
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
	if strings.TrimSpace(bundle.SignatureOrDigest) == "" {
		missing = append(missing, "bundle")
	}
	if len(missing) > 0 {
		return failCheck(id, "signature_or_digest is present", ReasonSignatureMissing, map[string]any{"missing": missing})
	}
	return passCheck(id, "signature_or_digest is present", map[string]any{})
}

func checkSourceCommitNotPlaceholder(bundle *ScienceClaimBundle, localDev bool) VerificationCheck {
	const id = "source_commit_not_placeholder"
	if localDev {
		return passCheck(id, "source_commit is not the 40-zero placeholder (release mode)",
			map[string]any{"local_dev": true})
	}
	var offenders []string
	check := func(name, commit string) {
		if strings.TrimSpace(commit) == ZeroSourceCommitPlaceholder {
			offenders = append(offenders, name)
		}
	}
	check("bundle", bundle.SourceCommit)
	for name, meta := range majorArtifacts(bundle) {
		if meta != nil {
			check(name, meta.SourceCommit)
		}
	}
	if len(offenders) > 0 {
		return failCheck(id, "source_commit is not the 40-zero placeholder unless local_dev = true",
			ReasonSourceCommitPlaceholder, map[string]any{"placeholder_commits": offenders})
	}
	return passCheck(id, "source_commit is not the 40-zero placeholder unless local_dev = true", map[string]any{})
}

func majorArtifacts(bundle *ScienceClaimBundle) map[string]*MajorArtifactMeta {
	out := map[string]*MajorArtifactMeta{
		"claim_artifact":  artifactMetaClaim(bundle.ClaimArtifact),
		"assumption_set":  artifactMetaAssumption(bundle.AssumptionSet),
		"runtime_receipt": artifactMetaReceipt(bundle.RuntimeReceipt),
		"evidence_bundle": artifactMetaEvidence(bundle.EvidenceBundle),
	}
	if certs := bundle.TraceCertificatesList(); len(certs) > 0 {
		out["trace_certificate"] = artifactMetaCert(certs[0])
	}
	return out
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
