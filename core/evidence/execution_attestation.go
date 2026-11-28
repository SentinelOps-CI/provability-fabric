// SPDX-License-Identifier: Apache-2.0

package evidence

import (
	"crypto/ed25519"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

const executionSignaturePrefix = "ed25519-execution-v1:"
const executionSignatureDomain = "provability-fabric/execution-attestation/v1\x00"

type executionTrust struct {
	Profile        string `json:"profile"`
	BundleID       string `json:"expected_bundle_id"`
	TraceDigest    string `json:"expected_trace_digest"`
	Attestor       string `json:"attestor"`
	PublicKey      string `json:"public_key_base64"`
}

type executionAttestation struct {
	SchemaVersion string      `json:"schema_version"`
	ID            string      `json:"attestation_id"`
	Attestor      string      `json:"attestor"`
	Ref           ArtifactRef `json:"signed_claim_ref"`
	Signature     string      `json:"signature"`
	MediaType     string      `json:"media_type,omitempty"`
}

func canonicalBase64(value string, size int) ([]byte, error) {
	raw, err := base64.StdEncoding.Strict().DecodeString(value)
	if err != nil || len(raw) != size || base64.StdEncoding.EncodeToString(raw) != value {
		return nil, fmt.Errorf("invalid canonical base64 value (expected %d bytes)", size)
	}
	return raw, nil
}

func validTraceDigest(value string) bool {
	if !strings.HasPrefix(value, DigestPrefix) || len(value) != len(DigestPrefix)+64 {
		return false
	}
	raw, err := hex.DecodeString(strings.TrimPrefix(value, DigestPrefix))
	return err == nil && len(raw) == 32 && value == DigestPrefix+hex.EncodeToString(raw)
}

// executionAttestationMessage commits to the selected bundle identity,
// attestor identity and exact trace reference. Each string is framed by
// its unsigned 64-bit network-order UTF-8 byte length. It intentionally
// excludes the signature and outer bundle digest (which includes it).
func executionAttestationMessage(bundle EvidenceBundle, att executionAttestation) []byte {
	message := []byte(executionSignatureDomain)
	for _, field := range []string{bundle.SchemaVersion, bundle.BundleID,
		att.SchemaVersion, att.ID, att.Attestor, att.Ref.Role, att.Ref.Path,
		att.Ref.MediaType, att.Ref.Digest, att.MediaType} {
		message = binary.BigEndian.AppendUint64(message, uint64(len(field)))
		message = append(message, field...)
	}
	return message
}

// verifyExecutionAttestations is called only after strict artifact and
// exact-reference verification. The trust file is selected by the verifier,
// never discovered from an untrusted bundle. The verifier must control the
// trust file and a stable artifact snapshot throughout validation.
func verifyExecutionAttestations(baseDir string, bundle EvidenceBundle, trustPath string) error {
	raw, err := os.ReadFile(trustPath)
	if err != nil {
		return fmt.Errorf("read execution attestation trust policy: %w", err)
	}
	if err := rejectAmbiguousReferenceJSON(raw); err != nil {
		return fmt.Errorf("ambiguous trust policy JSON: %w", err)
	}
	var policy executionTrust
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(raw, &fields); err != nil {
		return fmt.Errorf("decode execution trust policy: %w", err)
	}
	for _, field := range []string{"profile", "expected_bundle_id", "expected_trace_digest", "attestor", "public_key_base64"} {
		if _, ok := fields[field]; !ok {
			return fmt.Errorf("missing trust policy field %q", field)
		}
	}
	if len(fields) != 5 {
		return fmt.Errorf("unexpected execution trust policy field")
	}
	if err := json.Unmarshal(raw, &policy); err != nil {
		return fmt.Errorf("decode execution trust policy: %w", err)
	}
	if policy.Profile != "ed25519-execution-v1" || policy.BundleID == "" ||
		policy.Attestor == "" || !validTraceDigest(policy.TraceDigest) {
		return fmt.Errorf("invalid execution attestation trust policy")
	}
	key, err := canonicalBase64(policy.PublicKey, ed25519.PublicKeySize)
	if err != nil {
		return fmt.Errorf("execution attestation public key: %w", err)
	}
	if bundle.BundleID != policy.BundleID {
		return fmt.Errorf("unexpected execution bundle identity")
	}

	// Scope is deliberately one expected execution trace. Other artifact
	// roles are structurally checked but not cryptographically attested.
	var trace ArtifactRef
	traceCount := 0
	for _, ref := range bundle.Artifacts {
		if ref.Role == "execution-trace" {
			traceCount++
			trace = ref
		}
	}
	if traceCount != 1 || trace.Digest != policy.TraceDigest ||
		trace.MediaType != roleMediaTypes["execution-trace"] {
		return fmt.Errorf("expected exactly one externally identified execution trace")
	}
	count := 0
	for _, ref := range bundle.Artifacts {
		if ref.Role != "attestation" {
			continue
		}
		count++
		if ref.MediaType != roleMediaTypes["attestation"] {
			return fmt.Errorf("unexpected execution attestation media type")
		}
		p, err := resolveContainedExistingPath(baseDir, ref.Path)
		if err != nil {
			return err
		}
		raw, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		sum := sha256.Sum256(raw)
		if ref.Digest != DigestPrefix+hex.EncodeToString(sum[:]) {
			return fmt.Errorf("execution attestation changed after digest validation")
		}
		if err := rejectAmbiguousReferenceJSON(raw); err != nil {
			return err
		}
		var att executionAttestation
		if err := json.Unmarshal(raw, &att); err != nil {
			return err
		}
		if att.Attestor != policy.Attestor || att.Ref != trace {
			return fmt.Errorf("execution attestation %q does not match selected attestor and trace", att.ID)
		}
		if !strings.HasPrefix(att.Signature, executionSignaturePrefix) {
			return fmt.Errorf("execution attestation %q uses unsupported signature profile", att.ID)
		}
		sig, err := canonicalBase64(strings.TrimPrefix(att.Signature, executionSignaturePrefix), ed25519.SignatureSize)
		if err != nil {
			return err
		}
		if !ed25519.Verify(ed25519.PublicKey(key), executionAttestationMessage(bundle, att), sig) {
			return fmt.Errorf("execution attestation %q signature verification failed", att.ID)
		}
	}
	if count == 0 {
		return fmt.Errorf("execution attestation signature verification requires an attestation")
	}
	return nil
}
