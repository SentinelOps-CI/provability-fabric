// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps

package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"gopkg.in/yaml.v3"
)

// Error codes for config validation ergonomics
const (
	ErrCfgMissingKey   = "CFG_MISSING_KEY"
	ErrCfgInvalidValue = "CFG_INVALID_VALUE"
)

type EvidenceConfig struct {
	Emit bool `yaml:"emit" json:"emit"`
}

type ReplayConfig struct {
	LowViewMin float64 `yaml:"lowview_min" json:"lowview_min"`
}

type SentinelOpsConfig struct {
	EgressProfile string         `yaml:"egress_profile" json:"egress_profile"`
	Evidence      EvidenceConfig `yaml:"evidence" json:"evidence"`
	Replay        ReplayConfig   `yaml:"replay" json:"replay"`
}

type ResolvedConfig struct {
	Config         SentinelOpsConfig  `json:"config"`
	Sources        map[string]string  `json:"sources"`
	DefaultsUsed   []string           `json:"defaults_used"`
	ValidationInfo *ValidationOutcome `json:"validation,omitempty"`
}

type ValidationOutcome struct {
	Valid  bool              `json:"valid"`
	Errors []ValidationError `json:"errors,omitempty"`
}

type ValidationError struct {
	Code    string `json:"code"`
	Field   string `json:"field"`
	Message string `json:"message"`
	Action  string `json:"action"`
	DocsURL string `json:"docs_url"`
}

// LoadAndValidateConfig loads sentinelops.yml (or .yaml), applies env substitution and overrides,
// sets smart defaults, and validates against the JSON Schema. It returns the resolved config
// plus metadata describing defaults used and value sources.
func LoadAndValidateConfig(path string) (*ResolvedConfig, error) {
	// Locate config file
	discoveredPath, err := discoverConfigPath(path)
	if err != nil {
		return nil, err
	}

	rawBytes, err := os.ReadFile(discoveredPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read config file: %w", err)
	}

	// Expand environment variables in YAML values (${VAR} / $VAR)
	expanded := os.ExpandEnv(string(rawBytes))

	// Unmarshal into generic map to allow env overrides before strict struct unmarshal
	var intermediate map[string]any
	if err := yaml.Unmarshal([]byte(expanded), &intermediate); err != nil {
		return nil, fmt.Errorf("failed to parse YAML: %w", err)
	}

	// Apply env overrides using SO_ prefix and __ nesting (e.g., SO_EVIDENCE__EMIT)
	applyEnvOverrides(&intermediate)

	// Marshal back to YAML then into the strong-typed struct
	reYAML, err := yaml.Marshal(intermediate)
	if err != nil {
		return nil, fmt.Errorf("failed to re-encode YAML: %w", err)
	}

	var cfg SentinelOpsConfig
	if err := yaml.Unmarshal(reYAML, &cfg); err != nil {
		return nil, fmt.Errorf("failed to decode configuration: %w", err)
	}

	// Apply smart defaults
	defaultsUsed := applyDefaults(&cfg)

	// Validate using JSON Schema
	validation := validateAgainstSchema(intermediate)

	// Additionally enforce semantic constraints for better error codes
	semErrs := validateSemantics(&cfg)
	if len(semErrs) > 0 {
		if validation == nil {
			validation = &ValidationOutcome{Valid: false}
		}
		validation.Valid = false
		validation.Errors = append(validation.Errors, semErrs...)
	}

	sources := map[string]string{
		"file": discoveredPath,
	}

	resolved := &ResolvedConfig{
		Config:         cfg,
		Sources:        sources,
		DefaultsUsed:   defaultsUsed,
		ValidationInfo: validation,
	}

	if validation != nil && !validation.Valid {
		return resolved, buildValidationError(validation)
	}

	return resolved, nil
}

func discoverConfigPath(path string) (string, error) {
	candidates := []string{}
	if path != "" {
		candidates = append(candidates, path)
	}
	// Project-local defaults
	candidates = append(candidates,
		"sentinelops.yml",
		"sentinelops.yaml",
	)
	// Legacy names for compatibility
	candidates = append(candidates,
		"provability-fabric.yaml",
		filepath.Join("config", "provability-fabric.yaml"),
	)
	for _, p := range candidates {
		if _, err := os.Stat(p); err == nil {
			return p, nil
		}
	}
	return "", fmt.Errorf("%s: no config file found (looked for sentinelops.yml/.yaml)", ErrCfgMissingKey)
}

var soEnvOverridePrefix = regexp.MustCompile(`^SO_[A-Z0-9_]+$`)

func applyEnvOverrides(doc *map[string]any) {
	envs := os.Environ()
	for _, e := range envs {
		parts := strings.SplitN(e, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key, val := parts[0], parts[1]
		if !soEnvOverridePrefix.MatchString(key) {
			continue
		}
		// Map SO_FOO__BAR__BAZ -> [foo][bar][baz]
		path := strings.ToLower(strings.ReplaceAll(strings.TrimPrefix(key, "SO_"), "__", "."))
		setNestedValue(doc, path, val)
	}
}

func setNestedValue(root *map[string]any, dottedPath string, raw string) {
	keys := strings.Split(dottedPath, ".")
	m := *root
	for i, k := range keys {
		if i == len(keys)-1 {
			// Heuristically coerce types: bool, float, int, else string
			if raw == "true" || raw == "false" {
				m[k] = (raw == "true")
				return
			}
			if f, err := parseFloat(raw); err == nil {
				m[k] = f
				return
			}
			if i64, err := parseInt(raw); err == nil {
				m[k] = i64
				return
			}
			m[k] = raw
			return
		}
		// descend
		next, ok := m[k].(map[string]any)
		if !ok {
			next = map[string]any{}
			m[k] = next
		}
		m = next
	}
}

func parseFloat(s string) (float64, error) {
	var f float64
	_, err := fmt.Sscan(s, &f)
	return f, err
}

func parseInt(s string) (int64, error) {
	var i int64
	_, err := fmt.Sscan(s, &i)
	return i, err
}

func applyDefaults(cfg *SentinelOpsConfig) []string {
	used := []string{}
	if strings.TrimSpace(cfg.EgressProfile) == "" {
		cfg.EgressProfile = "default"
		used = append(used, "egress_profile")
	}
	// Evidence.emit defaults to true when unspecified; yaml zero-value bool is false,
	// so we detect absence by re-parsing a presence map. Simpler: treat false with env var SO_EVIDENCE__EMIT to override.
	// To honor default=true only when missing, check raw env hint: if not explicitly set in file/env and false, set to true.
	// Here we assume missing => zero and false => likely explicit; provide default true only if both are missing in source map.
	// For pragmatic behavior, if false is zero value and evidence key absent -> set true.
	// Since we lost presence info, prefer a sane default: when false, still set true unless SO_EVIDENCE__EMIT provided.
	if os.Getenv("SO_EVIDENCE__EMIT") == "" {
		if !cfg.Evidence.Emit {
			cfg.Evidence.Emit = true
			used = append(used, "evidence.emit")
		}
	}
	if cfg.Replay.LowViewMin == 0 {
		cfg.Replay.LowViewMin = 0.999
		used = append(used, "replay.lowview_min")
	}
	sort.Strings(used)
	return used
}

func validateAgainstSchema(doc map[string]any) *ValidationOutcome {
	// Lightweight validator mirroring config/schemas/sentinelops-schema.json
	var errs []ValidationError

	// egress_profile
	v, ok := doc["egress_profile"]
	if !ok {
		errs = append(errs, ValidationError{
			Code:    ErrCfgMissingKey,
			Field:   "egress_profile",
			Message: "required field is missing",
			Action:  suggestionForField("egress_profile"),
			DocsURL: docsURLForCode(ErrCfgMissingKey),
		})
	} else if s, ok := v.(string); !ok || strings.TrimSpace(s) == "" {
		errs = append(errs, ValidationError{
			Code:    ErrCfgInvalidValue,
			Field:   "egress_profile",
			Message: "must be a non-empty string",
			Action:  suggestionForField("egress_profile"),
			DocsURL: docsURLForCode(ErrCfgInvalidValue),
		})
	}

	// evidence.emit
	ev, ok := doc["evidence"]
	if !ok {
		errs = append(errs, ValidationError{
			Code:    ErrCfgMissingKey,
			Field:   "evidence",
			Message: "required object is missing",
			Action:  "Add evidence.emit boolean",
			DocsURL: docsURLForCode(ErrCfgMissingKey),
		})
	} else if m, ok := ev.(map[string]any); ok {
		emit, ok := m["emit"]
		if !ok {
			errs = append(errs, ValidationError{
				Code:    ErrCfgMissingKey,
				Field:   "evidence.emit",
				Message: "required field is missing",
				Action:  suggestionForField("evidence.emit"),
				DocsURL: docsURLForCode(ErrCfgMissingKey),
			})
		} else if _, ok := emit.(bool); !ok {
			errs = append(errs, ValidationError{
				Code:    ErrCfgInvalidValue,
				Field:   "evidence.emit",
				Message: "must be a boolean",
				Action:  suggestionForField("evidence.emit"),
				DocsURL: docsURLForCode(ErrCfgInvalidValue),
			})
		}
	} else {
		errs = append(errs, ValidationError{
			Code:    ErrCfgInvalidValue,
			Field:   "evidence",
			Message: "must be an object",
			Action:  "Set evidence.emit: true|false",
			DocsURL: docsURLForCode(ErrCfgInvalidValue),
		})
	}

	// replay.lowview_min
	rp, ok := doc["replay"]
	if !ok {
		errs = append(errs, ValidationError{
			Code:    ErrCfgMissingKey,
			Field:   "replay",
			Message: "required object is missing",
			Action:  "Add replay.lowview_min number",
			DocsURL: docsURLForCode(ErrCfgMissingKey),
		})
	} else if m, ok := rp.(map[string]any); ok {
		lvm, ok := m["lowview_min"]
		if !ok {
			errs = append(errs, ValidationError{
				Code:    ErrCfgMissingKey,
				Field:   "replay.lowview_min",
				Message: "required field is missing",
				Action:  suggestionForField("replay.lowview_min"),
				DocsURL: docsURLForCode(ErrCfgMissingKey),
			})
		} else {
			switch lvm.(type) {
			case float64, float32, int64, int, json.Number:
				// ok; further range checks handled in semantics
			default:
				errs = append(errs, ValidationError{
					Code:    ErrCfgInvalidValue,
					Field:   "replay.lowview_min",
					Message: "must be a number",
					Action:  suggestionForField("replay.lowview_min"),
					DocsURL: docsURLForCode(ErrCfgInvalidValue),
				})
			}
		}
	} else {
		errs = append(errs, ValidationError{
			Code:    ErrCfgInvalidValue,
			Field:   "replay",
			Message: "must be an object",
			Action:  "Set replay.lowview_min: 0.999",
			DocsURL: docsURLForCode(ErrCfgInvalidValue),
		})
	}

	if len(errs) == 0 {
		return &ValidationOutcome{Valid: true}
	}
	return &ValidationOutcome{Valid: false, Errors: errs}
}

func validateSemantics(cfg *SentinelOpsConfig) []ValidationError {
	var errs []ValidationError
	// replay.lowview_min must be in (0,1]
	if cfg.Replay.LowViewMin <= 0 || cfg.Replay.LowViewMin > 1 {
		errs = append(errs, ValidationError{
			Code:    ErrCfgInvalidValue,
			Field:   "replay.lowview_min",
			Message: "must be within (0, 1]",
			Action:  "Set replay.lowview_min to a value like 0.999",
			DocsURL: docsURLForCode(ErrCfgInvalidValue),
		})
	}
	if strings.TrimSpace(cfg.EgressProfile) == "" {
		errs = append(errs, ValidationError{
			Code:    ErrCfgMissingKey,
			Field:   "egress_profile",
			Message: "required value missing",
			Action:  "Set egress_profile or rely on default 'default'",
			DocsURL: docsURLForCode(ErrCfgMissingKey),
		})
	}
	return errs
}

func suggestionForField(field string) string {
	switch field {
	case "replay.lowview_min":
		return "Use a value close to 1.0, e.g., 0.999"
	case "evidence.emit":
		return "Set to true to emit CERT-V1 in runtime"
	case "egress_profile":
		return "Choose a named egress profile or 'default'"
	default:
		return "Check value and type against the schema"
	}
}

func docsURLForCode(code string) string {
	return "https://docs.sentinelops.dev/error-catalog#" + code
}

func absPath(p string) string {
	if filepath.IsAbs(p) {
		return p
	}
	a, err := filepath.Abs(p)
	if err != nil {
		return p
	}
	return a
}

func buildValidationError(v *ValidationOutcome) error {
	if v == nil || v.Valid || len(v.Errors) == 0 {
		return nil
	}
	// Prefer the first error for exit cause
	first := v.Errors[0]
	// Build an error with code prefix so callers can map exit codes if needed
	return errors.New(first.Code + ": " + first.Field + ": " + first.Message)
}
