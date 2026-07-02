// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/provability-fabric/core/crypto/dsse"
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintf(os.Stderr, "usage: dsse-verify <envelope.json> [expected-payload-type]\n")
		os.Exit(2)
	}
	data, err := os.ReadFile(os.Args[1])
	if err != nil {
		fmt.Fprintf(os.Stderr, "read envelope: %v\n", err)
		os.Exit(1)
	}
	env, err := dsse.ParseEnvelopeJSON(data)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse envelope: %v\n", err)
		os.Exit(1)
	}
	expected := dsse.AccessReceiptType
	if len(os.Args) > 2 {
		expected = os.Args[2]
	}
	result := dsse.VerifyEnvelope(env, expected)
	out, _ := json.Marshal(result)
	fmt.Println(string(out))
	if !result.Valid {
		os.Exit(1)
	}
}
