// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/santhosh-tekuri/jsonschema/v5"
)

func loadCompiledSchema(repoRoot, schemaFile string) (*jsonschema.Schema, error) {
	compiler := jsonschema.NewCompiler()
	names, err := listEmbeddedSchemaNames()
	if err != nil && repoRoot != "" {
		names, err = listConfigSchemaNames(repoRoot)
	}
	if err != nil {
		return nil, err
	}
	for _, name := range names {
		body, ok := readEmbeddedSchema(name)
		if !ok && repoRoot != "" {
			p := ResolveSchemaPath(repoRoot, name)
			if b, err := os.ReadFile(p); err == nil {
				body = string(b)
				ok = true
			}
		}
		if !ok {
			continue
		}
		if err := registerSchemaResource(compiler, name, body); err != nil {
			return nil, fmt.Errorf("register schema %s: %w", name, err)
		}
	}
	if _, ok := readEmbeddedSchema(schemaFile); !ok && repoRoot != "" {
		if _, err := os.Stat(ResolveSchemaPath(repoRoot, schemaFile)); err != nil {
			return nil, fmt.Errorf("schema not found: %s", schemaFile)
		}
	}
	return compiler.Compile(schemaFile)
}

func registerSchemaResource(compiler *jsonschema.Compiler, name, body string) error {
	if err := compiler.AddResource(name, strings.NewReader(body)); err != nil {
		return err
	}
	var meta struct {
		ID string `json:"$id"`
	}
	if err := json.Unmarshal([]byte(body), &meta); err == nil && meta.ID != "" {
		if err := compiler.AddResource(meta.ID, strings.NewReader(body)); err != nil {
			return err
		}
	}
	return nil
}

func listConfigSchemaNames(repoRoot string) ([]string, error) {
	dir := ResolveSchemaPath(repoRoot, "")
	dir = filepath.Dir(dir)
	entries, err := os.ReadDir(dir)
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

// ValidateDocumentAgainstSchema validates arbitrary JSON-compatible data.
func ValidateDocumentAgainstSchema(repoRoot, schemaFile string, doc any) error {
	schema, err := loadCompiledSchema(repoRoot, schemaFile)
	if err != nil {
		return err
	}
	return schema.Validate(doc)
}

// ValidateScienceClaimBundleValue validates an in-memory bundle against ScienceClaimBundle.v0 schema.
func ValidateScienceClaimBundleValue(repoRoot string, bundle *ScienceClaimBundle) error {
	if bundle == nil {
		return fmt.Errorf("bundle is nil")
	}
	raw, err := json.Marshal(bundle)
	if err != nil {
		return err
	}
	if keys, err := DetectLegacyBundleKeys(raw); err == nil && len(keys) > 0 {
		return &LegacyBundleError{Keys: keys}
	}
	var doc any
	if err := json.Unmarshal(raw, &doc); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	return ValidateDocumentAgainstSchema(repoRoot, "ScienceClaimBundle.v0.schema.json", doc)
}

// ValidateComputationProfileBundle validates slim computation-profile bundle JSON.
func ValidateComputationProfileBundle(repoRoot string, bundle *ScienceClaimBundle) error {
	if bundle == nil {
		return fmt.Errorf("bundle is nil")
	}
	raw, err := json.Marshal(bundle)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(raw, &doc); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	return ValidateDocumentAgainstSchema(repoRoot, "ScienceClaimBundle.computation.v0.schema.json", doc)
}

// ValidateScienceClaimBundleFile validates bundle bytes against ScienceClaimBundle.v0 schema.
func ValidateScienceClaimBundleFile(repoRoot, bundlePath string) error {
	data, err := os.ReadFile(bundlePath)
	if err != nil {
		return err
	}
	if keys, err := DetectLegacyBundleKeys(data); err == nil && len(keys) > 0 {
		return fmt.Errorf("%w", &LegacyBundleError{Keys: keys})
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

// ValidateHandoffManifestFile validates HandoffManifest.v0 JSON.
func ValidateHandoffManifestFile(repoRoot, path string) error {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}
	if err := ValidateDocumentAgainstSchema(repoRoot, "HandoffManifest.v0.schema.json", doc); err != nil {
		return err
	}
	var manifest HandoffManifest
	if err := json.Unmarshal(data, &manifest); err != nil {
		return err
	}
	return ValidateHandoffManifestSemantics(&manifest)
}

// ValidateReleaseChainValidationResult validates ReleaseChainValidationResult.v0.
func ValidateReleaseChainValidationResult(repoRoot string, result ReleaseChainValidationResult) error {
	var doc any
	raw, err := json.Marshal(result)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		return err
	}
	if err := ValidateDocumentAgainstSchema(repoRoot, "ReleaseChainValidationResult.v0.schema.json", doc); err != nil {
		return err
	}
	return ValidateReleaseChainValidationResultSemantics(&result)
}

// ValidatePCSBenchmarkRun validates a per-case pcs-core BenchmarkRun.v0.
func ValidatePCSBenchmarkRun(repoRoot string, run PCSBenchmarkRun) error {
	return validateBenchmarkDoc(repoRoot, "BenchmarkRun.v0.schema.json", run)
}

// ValidatePCSBenchmarkReport validates pcs-core BenchmarkReport.v0.
func ValidatePCSBenchmarkReport(repoRoot string, report PCSBenchmarkReport) error {
	return validateBenchmarkDoc(repoRoot, "BenchmarkReport.v0.schema.json", report)
}

// ValidatePCSFailureLocalizationResult validates pcs-core FailureLocalizationResult.v0.
func ValidatePCSFailureLocalizationResult(repoRoot string, report PCSFailureLocalizationResult) error {
	return validateBenchmarkDoc(repoRoot, "FailureLocalizationResult.v0.schema.json", report)
}

// ValidatePCSCoverageReport validates pcs-core CoverageReport.v0 (single metric).
func ValidatePCSCoverageReport(repoRoot string, report PCSCoverageReport) error {
	return validateBenchmarkDoc(repoRoot, "CoverageReport.v0.schema.json", report)
}

// ValidatePCSExplainQualityReport validates pcs-core ExplainQualityReport.v0.
func ValidatePCSExplainQualityReport(repoRoot string, report PCSExplainQualityReport) error {
	return validateBenchmarkDoc(repoRoot, "ExplainQualityReport.v0.schema.json", report)
}

// ValidateAdmissionBenchmarkCase validates admission_benchmark_case.v0 JSON.
func ValidateAdmissionBenchmarkCase(repoRoot string, c AdmissionBenchmarkCase) error {
	return validateBenchmarkDoc(repoRoot, "AdmissionBenchmarkCase.v0.schema.json", c)
}

func validateBenchmarkDoc(repoRoot, schemaFile string, v any) error {
	var doc any
	raw, err := json.Marshal(v)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		return err
	}
	return ValidateDocumentAgainstSchema(repoRoot, schemaFile, doc)
}
