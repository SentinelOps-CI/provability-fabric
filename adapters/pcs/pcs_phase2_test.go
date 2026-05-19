// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func pcsCoreExamples(t *testing.T, name string) string {
	t.Helper()
	candidates := []string{
		filepath.Join(pcsCoreRoot(t), "examples", name),
	}
	for _, c := range candidates {
		if c == "" {
			continue
		}
		if _, err := os.Stat(c); err == nil {
			return c
		}
	}
	t.Skip("pcs-core example not found: ", name)
	return ""
}

func validHandoffManifestPath(t *testing.T) string {
	t.Helper()
	local := labtrustReleaseFixture(t, "handoff_to_pf.json")
	if _, err := os.Stat(local); err == nil {
		return local
	}
	return pcsCoreExamples(t, "handoff_manifest.valid.json")
}

func validReleaseManifestPath(t *testing.T) string {
	t.Helper()
	local := labtrustReleaseFixture(t, "release_manifest.json")
	if _, err := os.Stat(local); err == nil {
		return local
	}
	return pcsCoreExamples(t, "release_manifest.valid.json")
}

func verifyWithLoadedHandoff(t *testing.T, loaded *pcs.LoadedHandoff) error {
	t.Helper()
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	registry := loadArtifactRegistry(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Handoff:         loaded,
		Registry:        registry,
	}
	_, err = pcs.VerifyScienceClaimBundle(path, bundle, opts)
	return err
}

func TestPFAcceptsValidHandoffManifest(t *testing.T) {
	handoffPath := validHandoffManifestPath(t)
	if handoffPath == "" {
		t.Skip()
	}
	loaded, err := pcs.LoadHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	if loaded.Manifest == nil {
		t.Fatal("expected HandoffManifest.v0")
	}
	if err := verifyWithLoadedHandoff(t, loaded); err != nil {
		t.Fatal(err)
	}
}

func TestPFRejectsHandoffBundleHashMismatch(t *testing.T) {
	handoffPath := validHandoffManifestPath(t)
	if handoffPath == "" {
		t.Skip()
	}
	loaded, err := pcs.LoadHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	loaded.Manifest.Invariants["certified_bundle_hash"] = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err = verifyWithLoadedHandoff(t, loaded)
	if err == nil {
		t.Fatal("expected verify to fail on certified_bundle_hash mismatch")
	}
	if !strings.Contains(err.Error(), "certified_bundle_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestPFRejectsHandoffCertificateIDMismatch(t *testing.T) {
	handoffPath := validHandoffManifestPath(t)
	if handoffPath == "" {
		t.Skip()
	}
	loaded, err := pcs.LoadHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	loaded.Manifest.Invariants["certificate_id"] = "cert-trace-00000000-0000-0000-0000-000000000000"
	err = verifyWithLoadedHandoff(t, loaded)
	if err == nil {
		t.Fatal("expected verify to fail on certificate_id mismatch")
	}
	if !strings.Contains(err.Error(), "certificate_id mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestPFRejectsHandoffTraceHashMismatch(t *testing.T) {
	handoffPath := validHandoffManifestPath(t)
	if handoffPath == "" {
		t.Skip()
	}
	loaded, err := pcs.LoadHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	loaded.Manifest.Invariants["trace_hash"] = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err = verifyWithLoadedHandoff(t, loaded)
	if err == nil {
		t.Fatal("expected verify to fail on trace_hash mismatch")
	}
	if !strings.Contains(err.Error(), "trace_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestPFRejectsWrongHandoffTarget(t *testing.T) {
	handoffPath := validHandoffManifestPath(t)
	if handoffPath == "" {
		t.Skip()
	}
	loaded, err := pcs.LoadHandoff(handoffPath)
	if err != nil {
		t.Fatal(err)
	}
	loaded.Manifest.ToComponent = "Scientific Memory"
	err = verifyWithLoadedHandoff(t, loaded)
	if err == nil {
		t.Fatal("expected verify to fail on wrong handoff target")
	}
	if !strings.Contains(err.Error(), "to_component") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestPFEmitsReleaseChainValidationResult(t *testing.T) {
	manifestPath := validReleaseManifestPath(t)
	if manifestPath == "" {
		t.Skip()
	}
	opts := pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot(t),
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:     loadReleaseManifest(t).PFSourceCommit,
		ReleaseMode:      true,
		Registry:         loadArtifactRegistry(t),
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	if result.ValidationID == "" {
		t.Fatal("validation_id required")
	}
}

func TestReleaseChainValidationResultValidatesAgainstPCSCore(t *testing.T) {
	manifestPath := validReleaseManifestPath(t)
	if manifestPath == "" {
		t.Skip()
	}
	opts := pcs.ReleaseChainVerifyOptions{RepoRoot: repoRoot(t), ValidatorVersion: pcs.DefaultVerifierVersion, SourceCommit: loadReleaseManifest(t).PFSourceCommit}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateReleaseChainValidationResult(repoRoot(t), result); err != nil {
		t.Fatal(err)
	}
}

func TestReleaseChainResultStatusProofCheckedOnValidChain(t *testing.T) {
	artifactDir := labtrustReleaseArtifactDir(t)
	if _, err := os.Stat(filepath.Join(artifactDir, "trace.json")); err != nil {
		t.Skip("full labtrust-release artifact dir required (pcs-core examples/labtrust-release)")
	}
	manifestPath := filepath.Join(artifactDir, "release_manifest.v0.json")
	if _, err := os.Stat(manifestPath); err != nil {
		manifestPath = validReleaseManifestPath(t)
	}
	if manifestPath == "" {
		t.Skip()
	}
	profile, _ := pcs.LoadAdmissionProfile("labtrust_qc_release")
	opts := pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot(t),
		ArtifactDir:      artifactDir,
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:     loadReleaseManifest(t).PFSourceCommit,
		Registry:         loadArtifactRegistry(t),
		ReleaseMode:      true,
		AdmissionProfile: profile,
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	if result.Status != pcs.StatusProofChecked {
		t.Fatalf("status=%s failure_codes=%v", result.Status, result.FailureCodes)
	}
}

func TestPFReleaseChainSkipsScientificMemoryImportReport(t *testing.T) {
	manifestPath := validReleaseManifestPath(t)
	if manifestPath == "" {
		t.Skip()
	}
	manifest, err := pcs.LoadReleaseManifest(manifestPath)
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range pcs.PFReleaseChainArtifactNames(manifest) {
		if n == "scientific_memory_import_report.json" {
			t.Fatal("scientific_memory_import_report.json must not be in PF admission artifact list")
		}
	}
}

func TestReleaseChainResultStatusRejectedOnHashMismatch(t *testing.T) {
	manifestPath := validReleaseManifestPath(t)
	if manifestPath == "" {
		t.Skip()
	}
	data, err := os.ReadFile(manifestPath)
	if err != nil {
		t.Fatal(err)
	}
	var manifest pcs.ReleaseManifest
	if err := json.Unmarshal(data, &manifest); err != nil {
		t.Fatal(err)
	}
	for name, entry := range manifest.Artifacts {
		entry.SHA256 = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
		manifest.Artifacts[name] = entry
		break
	}
	dir := t.TempDir()
	mPath := filepath.Join(dir, "release_manifest.json")
	out, _ := json.MarshalIndent(manifest, "", "  ")
	if err := os.WriteFile(mPath, out, 0644); err != nil {
		t.Fatal(err)
	}
	opts := pcs.ReleaseChainVerifyOptions{RepoRoot: repoRoot(t), ValidatorVersion: pcs.DefaultVerifierVersion}
	result, err := pcs.VerifyReleaseChainFromManifest(mPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	if result.Status != pcs.StatusRejected {
		t.Fatalf("expected Rejected, got %s", result.Status)
	}
}

func TestPFRejectsUnregisteredArtifactType(t *testing.T) {
	registry := minimalRegistryForBundle(t)
	delete(registry.Entries, "ScienceClaimBundle.v0")
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.ValidateBundleAgainstRegistry(bundle, registry, pcs.RegistryValidateOptions{ReleaseMode: true})
	if err == nil || !strings.Contains(err.Error(), "unregistered artifact type") {
		t.Fatalf("unexpected: %v", err)
	}
}

func TestPFRejectsWrongProducerForTraceCertificate(t *testing.T) {
	registry := minimalRegistryForBundle(t)
	for key, entry := range registry.Entries {
		if entry.ArtifactType == "TraceCertificate.v0" {
			entry.Producer = "wrong-producer"
			registry.Entries[key] = entry
			break
		}
	}
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.ValidateBundleAgainstRegistry(bundle, registry, pcs.RegistryValidateOptions{ReleaseMode: true})
	if err == nil || !strings.Contains(err.Error(), "producer mismatch") {
		t.Fatalf("unexpected: %v", err)
	}
}

func TestPFRejectsStatusNotAllowedByRegistry(t *testing.T) {
	path := labtrustReleaseFixture(t, "invalid_rejected_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	registry := minimalRegistryForBundle(t)
	err = pcs.ValidateBundleAgainstRegistry(bundle, registry, pcs.RegistryValidateOptions{ReleaseMode: true})
	if err == nil {
		t.Fatal("expected registry rejection")
	}
	if !strings.Contains(err.Error(), "not allowed") &&
		!strings.Contains(err.Error(), "certificate status") {
		t.Fatalf("unexpected: %v", err)
	}
}

func TestPFExecutesRegistrySemanticChecks(t *testing.T) {
	registry := minimalRegistryForBundle(t)
	for key, entry := range registry.Entries {
		if entry.ArtifactType == "ScienceClaimBundle.v0" {
			entry.SemanticChecks = pcs.RegistrySemanticChecks{
				{CheckID: "embedded_bundle_passes_science_claim_semantics"},
			}
			registry.Entries[key] = entry
			break
		}
	}
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.ValidateBundleAgainstRegistry(bundle, registry, pcs.RegistryValidateOptions{ReleaseMode: true})
	if err == nil || !strings.Contains(err.Error(), "was not executed in release mode") {
		t.Fatalf("unexpected: %v", err)
	}
}

func validArtifactRegistryPath(t *testing.T) string {
	t.Helper()
	local := labtrustReleaseFixture(t, "artifact_registry.json")
	if _, err := os.Stat(local); err == nil {
		return local
	}
	return pcsCoreExamples(t, "artifact_registry.valid.json")
}

func loadArtifactRegistry(t *testing.T) *pcs.ArtifactRegistry {
	t.Helper()
	reg, err := pcs.LoadArtifactRegistry(validArtifactRegistryPath(t))
	if err != nil {
		t.Fatal(err)
	}
	return reg
}

func releaseModeValidateOpts(t *testing.T) pcs.ValidateOptions {
	t.Helper()
	manifest := loadReleaseManifest(t)
	loaded, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	return pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Handoff:         loaded,
		Registry:        loadArtifactRegistry(t),
	}
}

func releaseModeFormalValidateOpts(t *testing.T) pcs.ValidateOptions {
	t.Helper()
	opts := releaseModeValidateOpts(t)
	profile, err := pcs.LoadAdmissionProfile("labtrust_qc_release")
	if err != nil {
		t.Fatal(err)
	}
	rm, err := pcs.LoadReleaseManifest(labtrustReleaseFixture(t, "release_manifest.v0.json"))
	if err != nil {
		t.Fatal(err)
	}
	opts.AdmissionProfile = profile
	opts.ReleaseManifest = rm
	opts.FormalChecks = loadFormalCheckInputs(t, "labtrust")
	return opts
}

func loadFormalCheckInputs(t *testing.T, workflow string) pcs.FormalCheckInputs {
	t.Helper()
	dir := filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "formal", workflow)
	in := pcs.FormalCheckInputs{
		ProofObligationsPath: filepath.Join(dir, "proof_obligation.v0.json"),
		LeanCheckResultPath:  filepath.Join(dir, "lean_check_result.v0.json"),
	}
	resolved, err := pcs.ResolveFormalCheckInputs(repoRoot(t), in)
	if err != nil {
		t.Fatal(err)
	}
	return resolved
}

func minimalRegistryForBundle(t *testing.T) *pcs.ArtifactRegistry {
	t.Helper()
	return loadArtifactRegistry(t)
}

func TestPFHashMatchesPCSCoreSignedBundleVector(t *testing.T) {
	vectorDir := pcsCoreHashVectorDir(t, "SignedScienceClaimBundle.v0")
	input := filepath.Join(vectorDir, "input.json")
	wantDigest, err := os.ReadFile(filepath.Join(vectorDir, "digest.txt"))
	if err != nil {
		t.Fatal(err)
	}
	got, err := pcs.CanonicalHashFromFile(input)
	if err != nil {
		t.Fatal(err)
	}
	if strings.TrimSpace(string(wantDigest)) != got {
		t.Fatalf("digest mismatch: got %s want %s", got, strings.TrimSpace(string(wantDigest)))
	}
}

func pcsCoreHashVectorDir(t *testing.T, artifact string) string {
	t.Helper()
	candidates := []string{
		filepath.Join(pcsCoreRoot(t), "python", "tests", "hash_vectors", artifact),
	}
	for _, c := range candidates {
		if _, err := os.Stat(filepath.Join(c, "input.json")); err == nil {
			return c
		}
	}
	t.Skip("pcs-core hash vector not found for ", artifact)
	return ""
}

func TestPFRejectsIllegalStatusTransition(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	if bundle.ClaimArtifact != nil {
		bundle.ClaimArtifact.Status = pcs.StatusRuntimeObserved
	}
	for _, cert := range bundle.Certificates {
		if cert != nil {
			cert.Status = pcs.StatusRuntimeObserved
		}
	}
	check := pcs.CheckStatusTransitionPolicy(bundle)
	if check.Status != pcs.CheckFailed {
		t.Fatalf("expected failed status transition check, got %s", check.Status)
	}
}

func TestPFRejectsStaleArtifact(t *testing.T) {
	path := labtrustReleaseFixture(t, "invalid_stale_artifact.json")
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := releaseModeValidateOpts(t)
	opts.Handoff = nil
	opts.AllowMissingHandoff = true
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if pcs.VerificationPassed(result) {
		t.Fatal("expected verification to fail for stale certificate")
	}
}

func TestPFRejectsRejectedCertificate(t *testing.T) {
	path := labtrustReleaseFixture(t, "invalid_rejected_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := releaseModeValidateOpts(t)
	opts.Handoff = nil
	opts.AllowMissingHandoff = true
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if pcs.VerificationPassed(result) {
		t.Fatal("expected verification to fail for rejected certificate")
	}
}
