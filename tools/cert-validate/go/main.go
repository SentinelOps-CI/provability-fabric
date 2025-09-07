// SPDX-License-Identifier: Apache-2.0
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
)

func main() {
	schemaPath := flag.String("schema", "external/CERT-V1/schema/cert-v1.schema.json", "Path to CERT-V1 schema")
	flag.Parse()
	files := flag.Args()
	if len(files) == 0 {
		fmt.Fprintln(os.Stderr, "Usage: cert-validate-go --schema <path> <files...>")
		os.Exit(2)
	}
	// Lightweight structural validation (subset; full JSON Schema can be layered later)
	total := 0
	invalid := 0
	_ = schemaPath // reserved for future jsonschema usage
	for _, f := range files {
		total++
		b, err := ioutil.ReadFile(f)
		if err != nil {
			fmt.Fprintf(os.Stderr, "read error: %s: %v\n", f, err)
			invalid++
			continue
		}
		var m map[string]interface{}
		if err := json.Unmarshal(b, &m); err != nil {
			fmt.Fprintf(os.Stderr, "invalid json: %s: %v\n", f, err)
			invalid++
			continue
		}
		required := []string{"bundle_id", "policy_hash", "proof_hash", "automata_hash", "labeler_hash", "ni_monitor", "permit_decision", "path_witness_ok", "label_derivation_ok", "epoch", "egress_profile"}
		ok := true
		for _, k := range required {
			if _, exists := m[k]; !exists {
				ok = false
				fmt.Fprintf(os.Stderr, "missing %s in %s\n", k, f)
			}
		}
		if !ok {
			invalid++
		}
	}
	if invalid > 0 {
		os.Exit(1)
	}
	fmt.Printf("{\"ok\":true,\"total\":%d,\"invalid\":0}\n", total)
}
