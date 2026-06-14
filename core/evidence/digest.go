// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
)

const SchemaVersion = "0.1"

// SchemaVersionV02 is the opt-in v0.2 bundle schema version.
const SchemaVersionV02 = "0.2"

// DigestPrefix is the required digest prefix for v0.1 artifacts.
const DigestPrefix = "sha256:"

// FileDigest returns sha256 digest of raw file bytes.
func FileDigest(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(data)
	return DigestPrefix + hex.EncodeToString(sum[:]), nil
}

// CanonicalJSONDigest hashes canonical JSON of v excluding excludeKey when set.
func CanonicalJSONDigest(v any, excludeKey string) (string, error) {
	m, err := toMap(v)
	if err != nil {
		return "", err
	}
	if excludeKey != "" {
		cloned := make(map[string]any, len(m))
		for k, val := range m {
			if k == excludeKey {
				continue
			}
			cloned[k] = val
		}
		m = cloned
	}
	data, err := MarshalCanonical(m)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(data)
	return DigestPrefix + hex.EncodeToString(sum[:]), nil
}

// MarshalCanonical emits UTF-8 JSON with recursively sorted object keys.
func MarshalCanonical(v any) ([]byte, error) {
	normalized, err := normalizeForCanonical(v)
	if err != nil {
		return nil, err
	}
	return json.Marshal(normalized)
}

func normalizeForCanonical(v any) (any, error) {
	switch t := v.(type) {
	case map[string]any:
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		out := make(map[string]any, len(t))
		for _, k := range keys {
			n, err := normalizeForCanonical(t[k])
			if err != nil {
				return nil, err
			}
			out[k] = n
		}
		return out, nil
	case []any:
		out := make([]any, len(t))
		for i, item := range t {
			n, err := normalizeForCanonical(item)
			if err != nil {
				return nil, err
			}
			out[i] = n
		}
		return out, nil
	default:
		return v, nil
	}
}

// toMap converts JSON-round-tripped values into map[string]any for stable hashing.
func toMap(v any) (map[string]any, error) {
	switch m := v.(type) {
	case map[string]any:
		return m, nil
	default:
		data, err := json.Marshal(v)
		if err != nil {
			return nil, err
		}
		var out map[string]any
		if err := json.Unmarshal(data, &out); err != nil {
			return nil, fmt.Errorf("value is not a JSON object: %w", err)
		}
		return out, nil
	}
}

// FindRepoRoot walks upward from start looking for specs/evidence/v0.1.
func FindRepoRoot(start string) (string, error) {
	dir, err := filepath.Abs(start)
	if err != nil {
		return "", err
	}
	for {
		candidate := filepath.Join(dir, "specs", "evidence", "v0.1", "schemas")
		if st, err := os.Stat(candidate); err == nil && st.IsDir() {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}
	return "", fmt.Errorf("repo root not found from %s", start)
}
