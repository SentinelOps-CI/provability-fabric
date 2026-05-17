// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"github.com/santhosh-tekuri/jsonschema/v5"
)

func loadCompiledSchema(repoRoot, schemaFile string) (*jsonschema.Schema, error) {
	compiler := jsonschema.NewCompiler()
	registered := false

	register := func(name, content string) error {
		if err := compiler.AddResource(name, strings.NewReader(content)); err != nil {
			return err
		}
		registered = true
		return nil
	}

	for _, sibling := range []string{
		"VerificationResult.v0.schema.json",
		"ScienceClaimBundle.v0.schema.json",
		"SignedScienceClaimBundle.v0.schema.json",
	} {
		if body, ok := readEmbeddedSchema(sibling); ok {
			_ = register(sibling, body)
		} else if repoRoot != "" {
			p := ResolveSchemaPath(repoRoot, sibling)
			if _, err := os.Stat(p); err == nil {
				_ = register(sibling, mustReadFile(p))
			}
		}
	}

	if body, ok := readEmbeddedSchema(schemaFile); ok {
		if err := register(schemaFile, body); err != nil {
			return nil, err
		}
	} else if repoRoot != "" {
		schemaPath := ResolveSchemaPath(repoRoot, schemaFile)
		if _, err := os.Stat(schemaPath); err != nil {
			return nil, fmt.Errorf("schema not found: %s (embedded and repo)", schemaFile)
		}
		if err := register(schemaFile, mustReadFile(schemaPath)); err != nil {
			return nil, err
		}
	} else {
		return nil, fmt.Errorf("schema not found: %s", schemaFile)
	}

	if !registered {
		return nil, fmt.Errorf("no schema resources registered for %s", schemaFile)
	}
	return compiler.Compile(schemaFile)
}

// ValidateDocumentAgainstSchema validates arbitrary JSON-compatible data.
func ValidateDocumentAgainstSchema(repoRoot, schemaFile string, doc any) error {
	schema, err := loadCompiledSchema(repoRoot, schemaFile)
	if err != nil {
		return err
	}
	return schema.Validate(doc)
}

func mustReadFile(path string) string {
	b, err := os.ReadFile(path)
	if err != nil {
		panic(err)
	}
	return string(b)
}

// ValidateScienceClaimBundleFile validates bundle bytes against ScienceClaimBundle.v0 schema.
func ValidateScienceClaimBundleFile(repoRoot, bundlePath string) error {
	data, err := os.ReadFile(bundlePath)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	return ValidateDocumentAgainstSchema(repoRoot, "ScienceClaimBundle.v0.schema.json", doc)
}

// ValidateVerificationResult validates a result against VerificationResult.v0 schema.
func ValidateVerificationResult(repoRoot string, result VerificationResult) error {
	var doc any
	raw, err := json.Marshal(result)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		return err
	}
	return ValidateDocumentAgainstSchema(repoRoot, "VerificationResult.v0.schema.json", doc)
}

// ValidateSignedScienceClaimBundle validates signed wrapper against schema.
func ValidateSignedScienceClaimBundle(repoRoot string, signed *SignedScienceClaimBundle) error {
	var doc any
	raw, err := json.Marshal(signed)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		return err
	}
	return ValidateDocumentAgainstSchema(repoRoot, "SignedScienceClaimBundle.v0.schema.json", doc)
}

// ValidateVerificationResultAlways validates using embedded schemas when repo root is unknown.
func ValidateVerificationResultAlways(result VerificationResult) error {
	return ValidateVerificationResult("", result)
}
