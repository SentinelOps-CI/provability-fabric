// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"fmt"
	"strings"
	"unicode"
)

// validateEvidencePathSegment keeps untrusted tenant and session identifiers
// to a single portable filesystem component. Confinement of symlink traversal
// is independently enforced by os.Root at the point of the filesystem write.
func validateEvidencePathSegment(field, value string) error {
	if value == "" || value == "." || value == ".." || len(value) > 255 ||
		strings.ContainsAny(value, "/\\:") || strings.IndexFunc(value, unicode.IsControl) >= 0 {
		return fmt.Errorf("invalid %s: expected a single nonempty path component", field)
	}
	return nil
}
