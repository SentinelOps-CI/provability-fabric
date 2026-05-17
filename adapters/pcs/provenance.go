// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"os"
	"strings"
)

func provenanceClaim(c *ClaimArtifact) *ArtifactProvenance {
	if c == nil {
		return nil
	}
	return &ArtifactProvenance{
		SourceRepo: c.SourceRepo, SourceCommit: c.SourceCommit,
		Status: c.Status, SignatureOrDigest: c.SignatureOrDigest,
	}
}

func provenanceAssumption(a *AssumptionSet) *ArtifactProvenance {
	if a == nil {
		return nil
	}
	return &ArtifactProvenance{
		SourceRepo: a.SourceRepo, SourceCommit: a.SourceCommit,
		Status: a.Status, SignatureOrDigest: a.SignatureOrDigest,
	}
}

func provenanceReceipt(r *RuntimeReceipt) *ArtifactProvenance {
	if r == nil {
		return nil
	}
	return &ArtifactProvenance{
		SourceRepo: r.SourceRepo, SourceCommit: r.SourceCommit,
		Status: r.Status, SignatureOrDigest: r.SignatureOrDigest,
	}
}

func provenanceCert(c *TraceCertificate) *ArtifactProvenance {
	if c == nil {
		return nil
	}
	return &ArtifactProvenance{
		SourceRepo: c.SourceRepo, SourceCommit: c.SourceCommit,
		Status: c.Status, SignatureOrDigest: c.SignatureOrDigest,
	}
}

func provenanceEvidence(e *EvidenceBundle) *ArtifactProvenance {
	if e == nil {
		return nil
	}
	return &ArtifactProvenance{
		SourceRepo: e.SourceRepo, SourceCommit: e.SourceCommit,
		Status: "", SignatureOrDigest: e.SignatureOrDigest,
	}
}

// ForbiddenPlaceholderCommits are rejected for PF outputs in release mode and for bundle
// verification when --release-mode is enabled (unless local_dev).
var ForbiddenPlaceholderCommits = []string{
	ZeroSourceCommitPlaceholder,
	"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
	"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
	"cccccccccccccccccccccccccccccccccccccccc",
	"dddddddddddddddddddddddddddddddddddddddd",
	"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
}

// IsForbiddenPlaceholderCommit reports whether commit is a known non-production placeholder.
func IsForbiddenPlaceholderCommit(commit string) bool {
	c := strings.ToLower(strings.TrimSpace(commit))
	if c == "" {
		return true
	}
	for _, p := range ForbiddenPlaceholderCommits {
		if c == p {
			return true
		}
	}
	return false
}

// ReleaseModeFromEnv is true when PF_RELEASE_MODE=1 or PCS_RELEASE_MODE=1.
func ReleaseModeFromEnv() bool {
	for _, key := range []string{"PF_RELEASE_MODE", "PCS_RELEASE_MODE"} {
		v := strings.TrimSpace(os.Getenv(key))
		if v == "1" || strings.EqualFold(v, "true") {
			return true
		}
	}
	return false
}

// ValidatePFProvenanceCommit enforces production provenance on PF-emitted artifacts.
func ValidatePFProvenanceCommit(commit string, releaseMode, localDev bool) error {
	if localDev {
		if releaseMode {
			return fmt.Errorf("release-mode cannot be combined with local-dev")
		}
		return nil
	}
	if !releaseMode {
		return nil
	}
	if IsForbiddenPlaceholderCommit(commit) {
		return fmt.Errorf("release-mode rejects placeholder source_commit %q", commit)
	}
	if len(strings.TrimSpace(commit)) != 40 {
		return fmt.Errorf("release-mode requires a 40-character git source_commit, got %q", commit)
	}
	return nil
}

// ResolveSourceCommitForMode resolves provenance and enforces release-mode rules when enabled.
func ResolveSourceCommitForMode(releaseMode, localDev bool) (string, error) {
	commit := ResolveSourceCommit()
	if err := ValidatePFProvenanceCommit(commit, releaseMode, localDev); err != nil {
		return "", err
	}
	return commit, nil
}
