// SPDX-License-Identifier: Apache-2.0

package main

import (
	"fmt"
	"os"
	"strings"
	"testing"
)

// Compare the actual pure decision function against the Lean-generated
// exhaustive partition. The Lean workflow supplies the required fixture.
func TestEvidenceScopeLeanMatrix(t *testing.T) {
	var lines []string
	for _, authenticated := range []bool{false, true} {
		for _, read := range []bool{false, true} {
			for _, write := range []bool{false, true} {
				for requested, tenant := range []string{"", "tenant-a", "tenant-b"} {
					for _, op := range []bool{false, true} {
						var credential *evidenceCredential
						if authenticated {
							credential = &evidenceCredential{tenant: "tenant-a", read: read, write: write}
						}
						result, allowed := evidenceScope(credential, tenant, op)
						code := 0
						if allowed {
							if result != "tenant-a" {
								t.Fatalf("unexpected effective tenant: %q", result)
							}
							code = 1
						} else if result != "" {
							t.Fatal("denial returned a tenant")
						}
						want := authenticated && ((op && write) || (!op && read)) && requested != 2
						if allowed != want {
							t.Fatal("scope decision differs from reference predicate")
						}
						lines = append(lines, fmt.Sprintf("CASE %t %t %t %d %t %d", authenticated, read, write, requested, op, code))
					}
				}
			}
		}
	}
	if len(lines) != 48 {
		t.Fatal("incomplete decision partition")
	}
	if path := os.Getenv("EVIDENCE_LEAN_MATRIX"); path != "" {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if strings.Join(lines, "\n")+"\n" != string(data) {
			t.Fatal("Go authorization decisions differ from Lean matrix")
		}
		t.Log("All 48 Go authorization decisions match Lean execution")
	}
}
