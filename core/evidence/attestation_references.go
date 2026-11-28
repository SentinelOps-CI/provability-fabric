// SPDX-License-Identifier: Apache-2.0

package evidence

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path"
	"strings"
	"unicode/utf8"
)

// rejectAmbiguousReferenceJSON prevents duplicate-key and invalid-Unicode
// aliases from influencing the interpreted reference identity. The depth
// bound applies to this opt-in reference profile, not the legacy validator.
func rejectAmbiguousReferenceJSON(raw []byte) error {
	if !utf8.Valid(raw) {
		return fmt.Errorf("invalid UTF-8")
	}
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	var walk func(int) error
	walk = func(depth int) error {
		if depth > 64 {
			return fmt.Errorf("reference JSON exceeds nesting limit")
		}
		tok, err := dec.Token()
		if err != nil {
			return err
		}
		switch x := tok.(type) {
		case string:
			if strings.ContainsRune(x, utf8.RuneError) {
				return fmt.Errorf("unsupported replacement character")
			}
		case json.Delim:
			switch x {
			case '{':
				seen := map[string]bool{}
				for dec.More() {
					keyToken, err := dec.Token()
					if err != nil {
						return err
					}
					key, ok := keyToken.(string)
					if !ok || strings.ContainsRune(key, utf8.RuneError) || seen[key] {
						return fmt.Errorf("ambiguous object key")
					}
					seen[key] = true
					if err := walk(depth + 1); err != nil {
						return err
					}
				}
			case '[':
				for dec.More() {
					if err := walk(depth + 1); err != nil {
						return err
					}
				}
			default:
				return fmt.Errorf("unexpected JSON delimiter")
			}
			_, err := dec.Token()
			return err
		}
		return nil
	}
	if err := walk(0); err != nil {
		return err
	}
	if _, err := dec.Token(); err != io.EOF {
		return fmt.Errorf("trailing or invalid JSON")
	}
	return nil
}

// validateAttestationReferences checks the exact four-field identity of each
// signed_claim_ref against a unique manifest entry. The caller has already
// validated all artifact digests and schemas. The bundle directory must be
// a stable snapshot under verifier control throughout validation.
func validateAttestationReferences(baseDir string, refs []ArtifactRef) error {
	byPath := make(map[string]ArtifactRef, len(refs))
	ids := map[string]bool{}
	for _, ref := range refs {
		if ref.Path == "." || path.IsAbs(ref.Path) || path.Clean(ref.Path) != ref.Path ||
			ref.Path == ".." || strings.HasPrefix(ref.Path, "../") ||
			strings.ContainsAny(ref.Path, "\\:") {
			return fmt.Errorf("noncanonical manifest path %q", ref.Path)
		}
		if _, found := byPath[ref.Path]; found {
			return fmt.Errorf("duplicate manifest path %q", ref.Path)
		}
		byPath[ref.Path] = ref
	}
	count := 0
	for _, ref := range refs {
		if ref.Role != "attestation" {
			continue
		}
		count++
		p, err := resolveContainedExistingPath(baseDir, ref.Path)
		if err != nil {
			return fmt.Errorf("resolve attestation: %w", err)
		}
		raw, err := os.ReadFile(p)
		if err != nil {
			return fmt.Errorf("read attestation: %w", err)
		}
		sum := sha256.Sum256(raw)
		if DigestPrefix+hex.EncodeToString(sum[:]) != ref.Digest {
			return fmt.Errorf("attestation changed after digest validation")
		}
		if err := rejectAmbiguousReferenceJSON(raw); err != nil {
			return fmt.Errorf("ambiguous attestation JSON: %w", err)
		}
		var att struct {
			ID  string      `json:"attestation_id"`
			Ref ArtifactRef `json:"signed_claim_ref"`
		}
		if err := json.Unmarshal(raw, &att); err != nil {
			return fmt.Errorf("decode attestation: %w", err)
		}
		if att.ID == "" || ids[att.ID] {
			return fmt.Errorf("missing or duplicate attestation ID %q", att.ID)
		}
		ids[att.ID] = true
		target, found := byPath[att.Ref.Path]
		if !found || target.Role == "attestation" || target != att.Ref {
			return fmt.Errorf("attestation %q signed_claim_ref does not match a non-attestation manifest entry", att.ID)
		}
	}
	if count == 0 {
		return fmt.Errorf("attestation reference verification requires at least one attestation")
	}
	return nil
}
