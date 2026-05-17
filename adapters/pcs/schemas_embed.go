// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"embed"
	"io/fs"
	"strings"
)

// Embedded PCS JSON schemas (mirror config/schemas/pcs for go install / out-of-tree use).
//
//go:embed schemas/*.json
var embeddedSchemas embed.FS

func readEmbeddedSchema(name string) (string, bool) {
	data, err := embeddedSchemas.ReadFile("schemas/" + name)
	if err != nil {
		return "", false
	}
	return string(data), true
}

// ListEmbeddedSchemaNamesForTest exposes embedded schema names for drift tests.
func ListEmbeddedSchemaNamesForTest() ([]string, error) {
	return listEmbeddedSchemaNames()
}

// ReadEmbeddedSchemaForTest exposes embedded schema bytes for drift tests.
func ReadEmbeddedSchemaForTest(name string) (string, bool) {
	return readEmbeddedSchema(name)
}

func listEmbeddedSchemaNames() ([]string, error) {
	entries, err := fs.ReadDir(embeddedSchemas, "schemas")
	if err != nil {
		return nil, err
	}
	var names []string
	for _, e := range entries {
		if !e.IsDir() && strings.HasSuffix(e.Name(), ".json") {
			names = append(names, e.Name())
		}
	}
	return names, nil
}
