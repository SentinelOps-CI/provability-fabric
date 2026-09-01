// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/santhosh-tekuri/jsonschema/v5"
)

// ValidationReport is the strict validation output artifact.
type ValidationReport struct {
	ReportID    string   `json:"report_id"`
	BundleRef   string   `json:"bundle_ref"`
	Status      string   `json:"status"`
	Errors      []string `json:"errors"`
	Warnings    []string `json:"warnings"`
	ValidatedAt string   `json:"validated_at"`
}

// ValidateOptions configures bundle validation.
type ValidateOptions struct {
	BundlePath string
	Strict     bool
	RepoRoot   string
	BaseDir    string
}

// ValidateBundle validates a v0.1 evidence bundle and returns a report.
func ValidateBundle(opts ValidateOptions) (*ValidationReport, error) {
	if opts.BaseDir == "" {
		opts.BaseDir = filepath.Dir(opts.BundlePath)
	}

	report := &ValidationReport{
		ReportID:    fmt.Sprintf("report-%d", time.Now().UTC().UnixNano()),
		BundleRef:   filepath.ToSlash(opts.BundlePath),
		Status:      "pass",
		Errors:      []string{},
		Warnings:    []string{},
		ValidatedAt: time.Now().UTC().Format(time.RFC3339),
	}

	if opts.RepoRoot == "" {
		root, err := FindRepoRoot(opts.BaseDir)
		if err != nil {
			root, err = FindRepoRoot(".")
		}
		if err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, err.Error())
			return report, err
		}
		opts.RepoRoot = root
	}

	data, err := os.ReadFile(opts.BundlePath)
	if err != nil {
		report.Status = "fail"
		report.Errors = append(report.Errors, err.Error())
		return report, err
	}

	var bundle EvidenceBundle
	if err := json.Unmarshal(data, &bundle); err != nil {
		report.Status = "fail"
		report.Errors = append(report.Errors, fmt.Sprintf("invalid bundle JSON: %v", err))
		return report, fmt.Errorf("invalid bundle JSON: %w", err)
	}

	schemaDir := filepath.Join(opts.RepoRoot, "specs", "evidence", schemaVersionDir(bundle.SchemaVersion), "schemas")
	schemaPath := filepath.Join(schemaDir, "evidence-bundle.schema.json")
	if err := validateAgainstSchema(schemaPath, data); err != nil {
		report.Status = "fail"
		report.Errors = append(report.Errors, err.Error())
		if opts.Strict {
			return report, err
		}
	}

	if bundle.SchemaVersion != SchemaVersion && bundle.SchemaVersion != SchemaVersionV02 {
		err := fmt.Errorf("unsupported schema_version %q", bundle.SchemaVersion)
		report.Status = "fail"
		report.Errors = append(report.Errors, err.Error())
		if opts.Strict {
			return report, err
		}
	}

	if opts.Strict && bundle.ReplayContext != nil {
		if err := validateReplayContext(opts.BaseDir, bundle.ReplayContext); err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, err.Error())
			return report, err
		}
	}

	expectedDigest, err := bundleDigest(bundle)
	if err != nil {
		report.Status = "fail"
		report.Errors = append(report.Errors, err.Error())
		if opts.Strict {
			return report, err
		}
	} else if bundle.BundleDigest != expectedDigest {
		err := fmt.Errorf("bundle_digest mismatch: expected %s got %s", expectedDigest, bundle.BundleDigest)
		report.Status = "fail"
		report.Errors = append(report.Errors, err.Error())
		if opts.Strict {
			return report, err
		}
	}

	for _, ref := range bundle.Artifacts {
		artifactPath, pathErr := resolveContainedExistingPath(opts.BaseDir, ref.Path)
		if pathErr != nil {
			msg := fmt.Errorf("invalid artifact path %s: %w", ref.Path, pathErr)
			report.Status = "fail"
			report.Errors = append(report.Errors, msg.Error())
			if opts.Strict {
				return report, msg
			}
			continue
		}
		actual, err := FileDigest(artifactPath)
		if err != nil {
			report.Status = "fail"
			report.Errors = append(report.Errors, err.Error())
			if opts.Strict {
				return report, err
			}
			continue
		}
		if actual != ref.Digest {
			msg := fmt.Errorf("digest mismatch for %s: expected %s got %s", ref.Path, ref.Digest, actual)
			report.Status = "fail"
			report.Errors = append(report.Errors, msg.Error())
			if opts.Strict {
				return report, msg
			}
		}

		if opts.Strict {
			if err := validateRoleArtifact(opts.RepoRoot, bundle.SchemaVersion, ref.Role, artifactPath); err != nil {
				report.Status = "fail"
				report.Errors = append(report.Errors, err.Error())
				return report, err
			}
		}
	}

	if report.Status == "fail" && opts.Strict {
		return report, fmt.Errorf("validation failed with %d error(s)", len(report.Errors))
	}
	return report, nil
}

func validateRoleArtifact(repoRoot, schemaVersion, role, artifactPath string) error {
	schemaName, ok := roleSchemaName(role)
	if !ok {
		return nil
	}
	body, err := os.ReadFile(artifactPath)
	if err != nil {
		return err
	}
	// Role artifact schemas are shared across v0.1 and v0.2 bundle versions.
	schemaPath := filepath.Join(repoRoot, "specs", "evidence", "v0.1", "schemas", schemaName)
	return validateAgainstSchema(schemaPath, body)
}

func schemaVersionDir(version string) string {
	if version == SchemaVersionV02 {
		return "v0.2"
	}
	return "v0.1"
}

func validateReplayContext(baseDir string, ctx *ReplayContext) error {
	if ctx.KitTracePath != "" {
		p, err := resolveContainedExistingPath(baseDir, ctx.KitTracePath)
		if err != nil {
			return fmt.Errorf("replay_context.kit_trace_path invalid: %w", err)
		}
		if st, err := os.Stat(p); err != nil {
			return fmt.Errorf("replay_context.kit_trace_path missing: %w", err)
		} else if st.IsDir() {
			return fmt.Errorf("replay_context.kit_trace_path is not a file: %s", ctx.KitTracePath)
		}
	}
	if ctx.FixturesPath != "" {
		p, err := resolveContainedExistingPath(baseDir, ctx.FixturesPath)
		if err != nil {
			return fmt.Errorf("replay_context.fixtures_path invalid: %w", err)
		}
		if st, err := os.Stat(p); err != nil {
			return fmt.Errorf("replay_context.fixtures_path missing: %w", err)
		} else if !st.IsDir() {
			return fmt.Errorf("replay_context.fixtures_path is not a directory: %s", ctx.FixturesPath)
		}
		if _, err := resolveContainedExistingPath(p, "env.json"); err != nil {
			return fmt.Errorf("replay_context.fixtures_path env.json invalid: %w", err)
		}
	}
	return nil
}

// resolveContainedExistingPath resolves an existing path and proves that both
// its lexical location and its symlink-resolved target remain inside baseDir.
// The returned path is absolute and symlink-resolved.
func resolveContainedExistingPath(baseDir, candidate string) (string, error) {
	if candidate == "" {
		return "", fmt.Errorf("path is empty")
	}

	baseAbs, err := filepath.Abs(baseDir)
	if err != nil {
		return "", fmt.Errorf("resolve base directory: %w", err)
	}
	baseReal, err := filepath.EvalSymlinks(baseAbs)
	if err != nil {
		return "", fmt.Errorf("resolve base directory symlinks: %w", err)
	}
	baseReal, err = filepath.Abs(baseReal)
	if err != nil {
		return "", fmt.Errorf("normalize base directory: %w", err)
	}

	pathValue := filepath.FromSlash(candidate)
	joined := pathValue
	if !filepath.IsAbs(pathValue) {
		joined = filepath.Join(baseAbs, pathValue)
	}
	joinedAbs, err := filepath.Abs(joined)
	if err != nil {
		return "", fmt.Errorf("resolve path: %w", err)
	}
	if err := ensurePathWithin(baseAbs, joinedAbs); err != nil {
		return "", fmt.Errorf("path escapes base directory: %w", err)
	}

	resolved, err := filepath.EvalSymlinks(joinedAbs)
	if err != nil {
		return "", fmt.Errorf("resolve path symlinks: %w", err)
	}
	resolvedAbs, err := filepath.Abs(resolved)
	if err != nil {
		return "", fmt.Errorf("normalize resolved path: %w", err)
	}
	if err := ensurePathWithin(baseReal, resolvedAbs); err != nil {
		return "", fmt.Errorf("resolved path escapes base directory: %w", err)
	}
	return resolvedAbs, nil
}

func ensurePathWithin(baseDir, candidate string) error {
	rel, err := filepath.Rel(baseDir, candidate)
	if err != nil {
		return err
	}
	if rel == ".." || strings.HasPrefix(rel, ".."+string(filepath.Separator)) || filepath.IsAbs(rel) {
		return fmt.Errorf("%s is outside %s", candidate, baseDir)
	}
	return nil
}

func roleSchemaName(role string) (string, bool) {
	switch role {
	case "claim":
		return "claim.schema.json", true
	case "proof":
		return "proof.schema.json", true
	case "attestation":
		return "attestation.schema.json", true
	case "execution-trace":
		return "execution-trace.schema.json", true
	default:
		return "", false
	}
}

func validateAgainstSchema(schemaPath string, document []byte) error {
	if _, err := os.Stat(schemaPath); err != nil {
		return fmt.Errorf("schema missing at %s", schemaPath)
	}
	compiler := jsonschema.NewCompiler()
	compiler.AssertFormat = true
	schemaDir := filepath.Dir(schemaPath)
	entries, err := os.ReadDir(schemaDir)
	if err != nil {
		return err
	}
	var targetID string
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".schema.json") {
			continue
		}
		p := filepath.Join(schemaDir, entry.Name())
		raw, readErr := os.ReadFile(p)
		if readErr != nil {
			return readErr
		}
		var meta struct {
			ID string `json:"$id"`
		}
		if err := json.Unmarshal(raw, &meta); err != nil {
			return err
		}
		if meta.ID == "" {
			return fmt.Errorf("schema %s missing $id", p)
		}
		if err := compiler.AddResource(meta.ID, strings.NewReader(string(raw))); err != nil {
			return err
		}
		if p == schemaPath {
			targetID = meta.ID
		}
	}
	if targetID == "" {
		return fmt.Errorf("unable to resolve schema id for %s", schemaPath)
	}
	schema, err := compiler.Compile(targetID)
	if err != nil {
		return fmt.Errorf("compile schema: %w", err)
	}
	var doc any
	if err := json.Unmarshal(document, &doc); err != nil {
		return fmt.Errorf("invalid JSON document: %w", err)
	}
	if err := schema.Validate(doc); err != nil {
		return fmt.Errorf("schema validation failed: %w", err)
	}
	return nil
}

// WriteValidationReport writes a validation report JSON file.
func WriteValidationReport(path string, report *ValidationReport) error {
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	data = append(data, '\n')
	return os.WriteFile(path, data, 0644)
}
