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

func pcsBenchIngestSchemaAliases(name string) []string {
	switch name {
	case "PcsBenchIngest.v0.schema.json":
		return []string{"PcsBenchIngest.v0.schema.json", "PCSBenchIngest.v0.schema.json"}
	case "PCSBenchIngest.v0.schema.json":
		return []string{"PCSBenchIngest.v0.schema.json", "PcsBenchIngest.v0.schema.json"}
	default:
		return []string{name}
	}
}

func readSchemaBody(repoRoot, name string) (string, bool) {
	if body, ok := readEmbeddedSchema(name); ok {
		return body, true
	}
	if repoRoot == "" {
		return "", false
	}
	for _, alias := range pcsBenchIngestSchemaAliases(name) {
		if b, err := os.ReadFile(ResolveSchemaPath(repoRoot, alias)); err == nil {
			return string(b), true
		}
	}
	return "", false
}

func loadCompiledSchema(repoRoot, schemaFile string) (*jsonschema.Schema, error) {
	compiler := jsonschema.NewCompiler()
	names, err := listEmbeddedSchemaNames()
	if err != nil && repoRoot != "" {
		names, err = listConfigSchemaNames(repoRoot)
	}
	if err != nil {
		return nil, err
	}
	registeredID := map[string]struct{}{}
	for _, name := range names {
		body, ok := readSchemaBody(repoRoot, name)
		if !ok {
			continue
		}
		for _, alias := range pcsBenchIngestSchemaAliases(name) {
			if err := compiler.AddResource(alias, strings.NewReader(body)); err != nil {
				return nil, fmt.Errorf("register schema %s: %w", alias, err)
			}
		}
		if err := registerSchemaID(compiler, body, registeredID); err != nil {
			return nil, fmt.Errorf("register schema %s: %w", name, err)
		}
	}
	if _, ok := readSchemaBody(repoRoot, schemaFile); !ok {
		return nil, fmt.Errorf("schema not found: %s", schemaFile)
	}
	return compiler.Compile(schemaFile)
}

func registerSchemaResource(compiler *jsonschema.Compiler, name, body string) error {
	if err := compiler.AddResource(name, strings.NewReader(body)); err != nil {
		return err
	}
	return registerSchemaID(compiler, body, nil)
}

func registerSchemaID(compiler *jsonschema.Compiler, body string, seen map[string]struct{}) error {
	var meta struct {
		ID string `json:"$id"`
	}
	if err := json.Unmarshal([]byte(body), &meta); err != nil || meta.ID == "" {
		return nil
	}
	if seen != nil {
		if _, ok := seen[meta.ID]; ok {
			return nil
		}
		seen[meta.ID] = struct{}{}
	}
	return compiler.AddResource(meta.ID, strings.NewReader(body))
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

func loadCompiledPCSCoreSchema(pcsCoreRoot, schemaFile string) (*jsonschema.Schema, error) {
	schemaDir := filepath.Join(pcsCoreRoot, "schemas")
	compiler := jsonschema.NewCompiler()
	entries, err := os.ReadDir(schemaDir)
	if err != nil {
		return nil, fmt.Errorf("read pcs-core schemas: %w", err)
	}
	for _, e := range entries {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".json") {
			continue
		}
		body, err := os.ReadFile(filepath.Join(schemaDir, e.Name()))
		if err != nil {
			return nil, err
		}
		if err := registerSchemaResource(compiler, e.Name(), string(body)); err != nil {
			return nil, fmt.Errorf("register pcs-core schema %s: %w", e.Name(), err)
		}
	}
	if _, err := os.Stat(filepath.Join(schemaDir, schemaFile)); err != nil {
		return nil, fmt.Errorf("pcs-core schema not found: %s", schemaFile)
	}
	return compiler.Compile(schemaFile)
}

// ValidateDocumentAgainstPCSCoreSchema validates data against schemas in pcs-core/schemas.
func ValidateDocumentAgainstPCSCoreSchema(pcsCoreRoot, schemaFile string, doc any) error {
	schema, err := loadCompiledPCSCoreSchema(pcsCoreRoot, schemaFile)
	if err != nil {
		return err
	}
	return schema.Validate(doc)
}

// pcsCoreHasSchema reports whether a schema file exists in pcs-core/schemas.
func pcsCoreHasSchema(pcsCoreRoot, schemaFile string) bool {
	if strings.TrimSpace(pcsCoreRoot) == "" {
		return false
	}
	st, err := os.Stat(filepath.Join(pcsCoreRoot, "schemas", schemaFile))
	return err == nil && !st.IsDir()
}

// pfOnlyBenchmarkSchemas are validated against PF embedded schemas (not shipped in pcs-core).
var pfOnlyBenchmarkSchemas = map[string]struct{}{
	"AdmissionBenchmarkCase.v0.schema.json": {},
}

// ValidateDocumentAgainstSchemaPreferPCSCore uses pcs-core/schemas when present, else PF embedded/config schemas.
func ValidateDocumentAgainstSchemaPreferPCSCore(pcsCoreRoot, repoRoot, schemaFile string, doc any) error {
	if _, pfOnly := pfOnlyBenchmarkSchemas[schemaFile]; !pfOnly && pcsCoreHasSchema(pcsCoreRoot, schemaFile) {
		return ValidateDocumentAgainstPCSCoreSchema(pcsCoreRoot, schemaFile, doc)
	}
	return ValidateDocumentAgainstSchema(repoRoot, schemaFile, doc)
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
