// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"strconv"
	"strings"
	"unicode/utf8"
)

const maxEvidenceJSONBytes = 4 << 20
const maxEvidenceJSONDepth = 64

// Preserve the existing Go float64 canonical wire representation only for
// decimal values that round-trip numerically unchanged. This rejects numeric
// aliases without silently changing existing representable signature bytes.
func canonicalEvidenceNumber(n json.Number) ([]byte, error) {
	raw := n.String()
	if len(raw) > 128 {
		return nil, fmt.Errorf("certificate number exceeds supported length")
	}
	if index := strings.IndexAny(raw, "eE"); index >= 0 {
		exponent, err := strconv.Atoi(raw[index+1:])
		if err != nil || exponent < -400 || exponent > 400 {
			return nil, fmt.Errorf("certificate number exponent outside supported range")
		}
	}
	value, err := n.Float64()
	if err != nil {
		return nil, fmt.Errorf("certificate number outside supported range")
	}
	encoded, err := json.Marshal(value)
	if err != nil {
		return nil, err
	}
	original, ok := new(big.Rat).SetString(raw)
	roundTrip, valid := new(big.Rat).SetString(string(encoded))
	if !ok || !valid || original.Cmp(roundTrip) != 0 {
		return nil, fmt.Errorf("certificate number would lose precision")
	}
	return encoded, nil
}

// Token-level parsing rejects duplicates at every depth before a map could
// collapse them. Replacement characters are refused to exclude lossy decoding
// of unpaired UTF-16 escapes. This intentionally restricts the legacy format.
func decodeEvidenceValue(raw []byte) (interface{}, error) {
	if len(raw) > maxEvidenceJSONBytes || !utf8.Valid(raw) {
		return nil, fmt.Errorf("unsupported certificate JSON encoding or size")
	}
	decoder := json.NewDecoder(bytes.NewReader(raw))
	decoder.UseNumber()
	value, err := readEvidenceToken(decoder, 0)
	if err != nil {
		return nil, err
	}
	if _, err := decoder.Token(); err != io.EOF {
		return nil, fmt.Errorf("trailing certificate JSON")
	}
	return value, nil
}

func decodeEvidenceObject(raw []byte) (map[string]interface{}, error) {
	value, err := decodeEvidenceValue(raw)
	if err != nil {
		return nil, err
	}
	obj, ok := value.(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("certificate payload must be an object")
	}
	return obj, nil
}

func readEvidenceToken(d *json.Decoder, depth int) (interface{}, error) {
	if depth > maxEvidenceJSONDepth {
		return nil, fmt.Errorf("certificate JSON nesting exceeds limit")
	}
	token, err := d.Token()
	if err != nil {
		return nil, err
	}
	switch v := token.(type) {
	case json.Delim:
		switch v {
		case '{':
			obj := make(map[string]interface{})
			for d.More() {
				keyToken, err := d.Token()
				if err != nil {
					return nil, err
				}
				key, ok := keyToken.(string)
				if !ok || strings.ContainsRune(key, utf8.RuneError) {
					return nil, fmt.Errorf("unsupported certificate key")
				}
				if _, exists := obj[key]; exists {
					return nil, fmt.Errorf("duplicate certificate key")
				}
				child, err := readEvidenceToken(d, depth+1)
				if err != nil {
					return nil, err
				}
				obj[key] = child
			}
			if end, err := d.Token(); err != nil || end != json.Delim('}') {
				return nil, fmt.Errorf("unterminated certificate object")
			}
			return obj, nil
		case '[':
			items := make([]interface{}, 0)
			for d.More() {
				child, err := readEvidenceToken(d, depth+1)
				if err != nil {
					return nil, err
				}
				items = append(items, child)
			}
			if end, err := d.Token(); err != nil || end != json.Delim(']') {
				return nil, fmt.Errorf("unterminated certificate array")
			}
			return items, nil
		default:
			return nil, fmt.Errorf("unexpected JSON delimiter")
		}
	case json.Number:
		if _, err := canonicalEvidenceNumber(v); err != nil {
			return nil, err
		}
		return v, nil
	case string:
		if strings.ContainsRune(v, utf8.RuneError) {
			return nil, fmt.Errorf("unsupported certificate string encoding")
		}
	}
	return token, nil
}
