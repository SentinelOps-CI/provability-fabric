// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

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
