// SPDX-License-Identifier: Apache-2.0

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestCanonicalJSONStableKeyOrder(t *testing.T) {
	in := map[string]any{
		"z": 1,
		"a": map[string]any{"y": 2, "b": 3},
	}
	first, err := pcs.CanonicalJSON(in)
	if err != nil {
		t.Fatal(err)
	}
	second, err := pcs.CanonicalJSON(in)
	if err != nil {
		t.Fatal(err)
	}
	if string(first) != string(second) {
		t.Fatalf("canonical JSON not stable:\n%s\n%s", first, second)
	}
	if string(first) != `{"a":{"b":3,"y":2},"z":1}` {
		t.Fatalf("unexpected canonical form: %s", first)
	}
}
