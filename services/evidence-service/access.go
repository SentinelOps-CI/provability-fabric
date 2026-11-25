// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"crypto/sha256"
	"crypto/subtle"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"

	"github.com/gin-gonic/gin"
)

// Each credential is bound to one tenant and explicit operation permissions.
// Store only the digest of a cryptographically random 32-byte bearer token.
type evidenceCredential struct {
	tenant string
	digest [sha256.Size]byte
	read   bool
	write  bool
}

type evidenceAccessEntry struct {
	Tenant      string `json:"tenant"`
	TokenSHA256 string `json:"token_sha256"`
	Read        bool   `json:"read"`
	Write       bool   `json:"write"`
}

func loadEvidenceAccess(path string) ([]evidenceCredential, error) {
	if path == "" {
		return nil, nil // Protected routes are unavailable until provisioned.
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read credential configuration: %w", err)
	}
	decoder := json.NewDecoder(bytes.NewReader(raw))
	decoder.DisallowUnknownFields()
	var entries []evidenceAccessEntry
	if err := decoder.Decode(&entries); err != nil {
		return nil, fmt.Errorf("invalid credential configuration JSON")
	}
	if err := decoder.Decode(new(interface{})); err != io.EOF {
		return nil, fmt.Errorf("unexpected trailing credential configuration")
	}
	if len(entries) == 0 {
		return nil, fmt.Errorf("credential configuration must contain entries")
	}
	credentials := make([]evidenceCredential, 0, len(entries))
	seen := make(map[[sha256.Size]byte]bool)
	for i, entry := range entries {
		if err := validateEvidencePathSegment("tenant", entry.Tenant); err != nil {
			return nil, fmt.Errorf("invalid credential tenant at entry %d", i)
		}
		if !entry.Read && !entry.Write {
			return nil, fmt.Errorf("credential entry %d has no permissions", i)
		}
		digest, err := hex.DecodeString(entry.TokenSHA256)
		if err != nil || len(digest) != sha256.Size || hex.EncodeToString(digest) != entry.TokenSHA256 {
			return nil, fmt.Errorf("invalid credential digest at entry %d", i)
		}
		var key [sha256.Size]byte
		copy(key[:], digest)
		if seen[key] {
			return nil, fmt.Errorf("duplicate credential digest at entry %d", i)
		}
		seen[key] = true
		credentials = append(credentials, evidenceCredential{
			tenant: entry.Tenant, digest: key, read: entry.Read, write: entry.Write,
		})
	}
	return credentials, nil
}

// Authenticate the canonical unpadded base64url encoding of 32 random bytes.
func (s *EvidenceService) authorizeEvidence(c *gin.Context, requestedTenant string, write bool) (string, bool) {
	if len(s.access) == 0 {
		writeError(c, http.StatusServiceUnavailable, "EVIDENCE_ACCESS_UNAVAILABLE",
			"No evidence access credentials are configured", "Provision operator-owned credentials", "")
		return "", false
	}
	values := c.Request.Header.Values("Authorization")
	var token []byte
	if len(values) == 1 {
		fields := strings.Fields(values[0])
		if len(fields) == 2 && strings.EqualFold(fields[0], "Bearer") && len(fields[1]) == 43 {
			decoded, err := base64.RawURLEncoding.Strict().DecodeString(fields[1])
			if err == nil && len(decoded) == 32 {
				token = decoded
			}
		}
	}
	var credential *evidenceCredential
	if token != nil {
		digest := sha256.Sum256(token)
		for i := range s.access {
			if subtle.ConstantTimeCompare(digest[:], s.access[i].digest[:]) == 1 {
				credential = &s.access[i]
			}
		}
	}
	if credential == nil {
		c.Header("WWW-Authenticate", "Bearer")
		writeError(c, http.StatusUnauthorized, "EVIDENCE_AUTH_REQUIRED",
			"Missing or invalid evidence credential", "Supply an authorized bearer credential", "")
		return "", false
	}
	tenant, ok := evidenceScope(credential, requestedTenant, write)
	if !ok {
		writeError(c, http.StatusForbidden, "EVIDENCE_ACCESS_DENIED",
			"Credential does not authorize the requested tenant or operation", "Use the authorized tenant and permission", "")
		return "", false
	}
	return tenant, true
}

// evidenceScope is the authorization decision after credential recognition.
func evidenceScope(credential *evidenceCredential, requestedTenant string, write bool) (string, bool) {
	if credential == nil || (write && !credential.write) || (!write && !credential.read) ||
		(requestedTenant != "" && requestedTenant != credential.tenant) {
		return "", false
	}
	return credential.tenant, true
}
