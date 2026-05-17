// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"fmt"
	"os"
	"strings"

	"github.com/google/uuid"
)

// uuidNew is isolated for tests that stub randomness later.
var uuidNew = uuid.NewString

const fixtureSourceCommit = "cccccccccccccccccccccccccccccccccccccccc"

// DeterministicMode is true when fixture freeze / CI should emit stable IDs and timestamps.
func DeterministicMode() bool {
	if v := strings.TrimSpace(os.Getenv("PF_DETERMINISTIC")); v == "1" || strings.EqualFold(v, "true") {
		return true
	}
	if v := strings.TrimSpace(os.Getenv("PCS_DETERMINISTIC")); v == "1" || strings.EqualFold(v, "true") {
		return true
	}
	return strings.TrimSpace(os.Getenv("PF_SOURCE_COMMIT")) == fixtureSourceCommit
}

func deterministicUUID(namespace, seed string) string {
	sum := sha256.Sum256([]byte(namespace + "\x00" + seed))
	var u uuid.UUID
	copy(u[:], sum[:16])
	u[6] = (u[6] & 0x0f) | 0x40
	u[8] = (u[8] & 0x3f) | 0x80
	return u.String()
}

func newVerificationID(bundleID string) string {
	if DeterministicMode() {
		return "verification-" + deterministicUUID("verification", bundleID)
	}
	return fmt.Sprintf("verification-%s", uuidNew())
}

func newSignedBundleID(bundleID, verificationID string) string {
	if DeterministicMode() {
		return "signed-" + deterministicUUID("signed", bundleID+"\x00"+verificationID)
	}
	return fmt.Sprintf("signed-%s", uuidNew())
}

func deterministicRFC3339(bundle *ScienceClaimBundle) string {
	if bundle != nil {
		if ts := strings.TrimSpace(bundle.CreatedAt); ts != "" {
			return ts
		}
	}
	return "2026-05-16T12:00:00Z"
}
