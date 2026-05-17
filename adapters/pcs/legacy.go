// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
)

// Legacy bundle keys rejected by pf verify (pcs-core uses runtime_receipts / certificates arrays).
var legacyBundleKeys = []string{
	"runtime_receipt",
	"trace_certificate",
	"trace_certificates",
}

// DetectLegacyBundleKeys returns legacy top-level field names present in raw bundle JSON.
func DetectLegacyBundleKeys(data []byte) ([]string, error) {
	var doc map[string]json.RawMessage
	if err := json.Unmarshal(data, &doc); err != nil {
		return nil, err
	}
	var found []string
	for _, key := range legacyBundleKeys {
		if _, ok := doc[key]; ok {
			found = append(found, key)
		}
	}
	return found, nil
}

// MigrateLegacyBundle converts a pre-pcs-core PF bundle JSON document to canonical array shape.
// Intended for offline migration tooling only; pf verify does not accept legacy input.
func MigrateLegacyBundle(data []byte) ([]byte, error) {
	var doc map[string]any
	if err := json.Unmarshal(data, &doc); err != nil {
		return nil, err
	}
	if keys, _ := DetectLegacyBundleKeys(data); len(keys) == 0 {
		return data, nil
	}
	if rr, ok := doc["runtime_receipt"]; ok {
		doc["runtime_receipts"] = []any{rr}
		delete(doc, "runtime_receipt")
	}
	var certs []any
	if tc, ok := doc["trace_certificate"]; ok {
		certs = append(certs, tc)
		delete(doc, "trace_certificate")
	}
	if tcs, ok := doc["trace_certificates"].([]any); ok {
		certs = append(certs, tcs...)
		delete(doc, "trace_certificates")
	}
	if len(certs) > 0 {
		doc["certificates"] = certs
	}
	if sv, ok := doc["schema_version"].(string); ok && sv == "ScienceClaimBundle.v0" {
		doc["schema_version"] = SchemaVersionV0
	}
	out, err := json.MarshalIndent(doc, "", "  ")
	if err != nil {
		return nil, err
	}
	return out, nil
}

// LegacyBundleError describes why a legacy bundle cannot be verified directly.
type LegacyBundleError struct {
	Keys []string
}

func (e *LegacyBundleError) Error() string {
	return fmt.Sprintf("legacy pcs bundle format (use runtime_receipts and certificates): %v", e.Keys)
}
