// SPDX-License-Identifier: Apache-2.0

package evidence

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestRequireAttestationReferences(t *testing.T) {
	root := repoRoot(t)
	for _, tc := range []struct {
		name string
		want string
	}{
		{"valid", ""},
		{"wrong-digest", "signed_claim_ref"},
		{"wrong-role", "signed_claim_ref"},
		{"wrong-media", "signed_claim_ref"},
		{"missing-target", "signed_claim_ref"},
		{"self-reference", "signed_claim_ref"},
		{"duplicate-path", "duplicate manifest path"},
		{"no-attestation", "at least one attestation"},
		{"duplicate-json-key", "ambiguous attestation JSON"},
		{"duplicate-bundle-key", "ambiguous bundle JSON"},
		{"noncanonical-path", "noncanonical manifest path"},
		{"non-strict", "requires strict"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			write := func(name string, data []byte) {
				t.Helper()
				if err := os.WriteFile(filepath.Join(dir, name), data, 0600); err != nil {
					t.Fatal(err)
				}
			}
			proof, err := os.ReadFile(filepath.Join(root, "specs", "evidence", "v0.1", "examples", "valid", "artifacts", "proof.json"))
			if err != nil {
				t.Fatal(err)
			}
			write("proof.json", proof)
			digest, err := FileDigest(filepath.Join(dir, "proof.json"))
			if err != nil {
				t.Fatal(err)
			}
			target := ArtifactRef{Role: "proof", Path: "proof.json", MediaType: roleMediaTypes["proof"], Digest: digest}
			signed := target
			switch tc.name {
			case "wrong-digest":
				signed.Digest = "sha256:" + strings.Repeat("0", 64)
			case "wrong-role":
				signed.Role = "claim"
			case "wrong-media":
				signed.MediaType = "application/json"
			case "missing-target":
				signed.Path = "unlisted.json"
				write("unlisted.json", proof)
			case "self-reference":
				signed.Path = "attestation.json"
				signed.Role = "attestation"
			case "noncanonical-path":
				target.Path = "./proof.json"
				signed.Path = target.Path
			}
			body, err := json.Marshal(map[string]any{
				"schema_version": "0.1",
				"attestation_id": "fixture-attestation",
				"attestor": "fixture-attestor",
				"signed_claim_ref": signed,
				"signature": "unsigned-test-placeholder",
			})
			if err != nil {
				t.Fatal(err)
			}
			if tc.name == "duplicate-json-key" {
				body = []byte(strings.Replace(string(body), `"attestor":"fixture-attestor"`, `"attestor":"other","attestor":"fixture-attestor"`, 1))
			}
			write("attestation.json", body)
			attDigest, err := FileDigest(filepath.Join(dir, "attestation.json"))
			if err != nil {
				t.Fatal(err)
			}
			refs := []ArtifactRef{target}
			if tc.name != "no-attestation" {
				refs = append(refs, ArtifactRef{Role: "attestation", Path: "attestation.json", MediaType: roleMediaTypes["attestation"], Digest: attDigest})
			}
			if tc.name == "duplicate-path" {
				refs = append(refs, target)
			}
			bundle := EvidenceBundle{
				BundleID: "reference-test", SchemaVersion: SchemaVersion,
				CreatedAt: "2025-01-01T00:00:00Z", Producer: "test",
				Artifacts: refs,
			}
			bundle.BundleDigest, err = bundleDigest(bundle)
			if err != nil {
				t.Fatal(err)
			}
			raw, err := json.Marshal(bundle)
			if err != nil {
				t.Fatal(err)
			}
			if tc.name == "duplicate-bundle-key" {
				raw = []byte(strings.Replace(string(raw), `"producer":"test"`, `"producer":"other","producer":"test"`, 1))
			}
			write("bundle.json", raw)
			opts := ValidateOptions{
				BundlePath: filepath.Join(dir, "bundle.json"),
				Strict: tc.name != "non-strict", RepoRoot: root, BaseDir: dir,
				RequireAttestationReferences: true,
			}
			report, err := ValidateBundle(opts)
			if tc.want == "" {
				if err != nil || report.Status != "pass" || len(report.Warnings) != 1 {
					t.Fatalf("valid reference failed: report=%+v err=%v", report, err)
				}
				return
			}
			if err == nil || report.Status != "fail" || !strings.Contains(strings.Join(report.Errors, " "), tc.want) {
				t.Fatalf("expected %q failure: report=%+v err=%v", tc.want, report, err)
			}
		})
	}
}
