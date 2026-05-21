// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// producerEmbeddedRefFields mirrors pcs-core PRODUCER_EMBEDDED_REF_FIELDS.
var producerEmbeddedRefFields = map[string][]string{
	"labtrust-gym":         {"benchmark_runs"},
	"certifyedge":          {"coverage_reports"},
	"provability-fabric":   {"explain_quality_reports", "profile_coverage_reports"},
	"scientific-memory":    {"explain_quality_reports"},
}

var ingestEmbeddedArrayTypes = map[string]string{
	"BenchmarkRun.v0":                 "benchmark_runs",
	"CoverageReport.v0":               "coverage_reports",
	"FailureLocalizationResult.v0":    "failure_localization_reports",
	"ExplainQualityReport.v0":         "explain_quality_reports",
	"ProfileCoverageReport.v0":        "profile_coverage_reports",
}

var allowedBenchIngestProducers = map[string]struct{}{
	"pcs-core":            {},
	"pcs-bench":           {},
	"labtrust-gym":        {},
	"certifyedge":         {},
	"provability-fabric":  {},
	"scientific-memory":   {},
}

// ValidatePCSBenchIngestSemantics applies pcs-core benchmark ingest semantic rules.
func ValidatePCSBenchIngestSemantics(ingest PCSBenchIngestV0) error {
	var errs []string
	if _, ok := allowedBenchIngestProducers[ingest.ProducerID]; !ok {
		errs = append(errs, fmt.Sprintf("unknown producer_id %q", ingest.ProducerID))
	}
	for _, field := range []string{
		"benchmark_runs",
		"coverage_reports",
		"failure_localization_reports",
		"explain_quality_reports",
		"profile_coverage_reports",
		"commands",
		"logs",
	} {
		switch field {
		case "benchmark_runs":
			if ingest.BenchmarkRuns == nil {
				errs = append(errs, "benchmark_runs must be a list")
			}
		case "coverage_reports":
			if ingest.CoverageReports == nil {
				errs = append(errs, "coverage_reports must be a list")
			}
		case "failure_localization_reports":
			if ingest.FailureLocalizationReports == nil {
				errs = append(errs, "failure_localization_reports must be a list")
			}
		case "explain_quality_reports":
			if ingest.ExplainQualityReports == nil {
				errs = append(errs, "explain_quality_reports must be a list")
			}
		case "profile_coverage_reports":
			if ingest.ProfileCoverageReports == nil {
				errs = append(errs, "profile_coverage_reports must be a list")
			}
		case "commands":
			if ingest.Commands == nil {
				errs = append(errs, "commands must be a list")
			}
		case "logs":
			if ingest.Logs == nil {
				errs = append(errs, "logs must be a list")
			}
		}
	}
	producerFields := producerEmbeddedRefFields[ingest.ProducerID]
	hasProducerEmbedded := false
	for _, field := range producerFields {
		switch field {
		case "benchmark_runs":
			if len(ingest.BenchmarkRuns) > 0 {
				hasProducerEmbedded = true
			}
		case "coverage_reports":
			if len(ingest.CoverageReports) > 0 {
				hasProducerEmbedded = true
			}
		case "explain_quality_reports":
			if len(ingest.ExplainQualityReports) > 0 {
				hasProducerEmbedded = true
			}
		case "profile_coverage_reports":
			if len(ingest.ProfileCoverageReports) > 0 {
				hasProducerEmbedded = true
			}
		}
	}
	if hasProducerEmbedded && len(ingest.ArtifactRefs) == 0 {
		errs = append(errs, fmt.Sprintf("producer %q requires artifact_refs when exporting embedded artifacts", ingest.ProducerID))
		return joinSemanticErrors(errs)
	}
	if len(ingest.ArtifactRefs) == 0 {
		return joinSemanticErrors(errs)
	}
	paths := map[string]struct{}{}
	refKeys := map[string]struct{}{}
	for i, ref := range ingest.ArtifactRefs {
		if err := validateBenchmarkArtifactRefSemantics(ref); err != nil {
			errs = append(errs, fmt.Sprintf("artifact_refs[%d]: %v", i, err))
			continue
		}
		if ref.Path != "" {
			if _, dup := paths[ref.Path]; dup {
				errs = append(errs, "artifact_refs contains duplicate path values")
			}
			paths[ref.Path] = struct{}{}
		}
		embedded := embeddedIngestObjects(ingest, ref.ArtifactType)
		if len(embedded) == 0 {
			errs = append(errs, fmt.Sprintf("artifact_refs[%d]: no embedded objects for %q", i, ref.ArtifactType))
			continue
		}
		if !digestMatchesEmbedded(ref.SHA256, embedded) {
			errs = append(errs, fmt.Sprintf(
				"artifact_refs[%d]: sha256 does not match any embedded %s signature_or_digest",
				i, ref.ArtifactType,
			))
		} else {
			refKeys[ref.ArtifactType+"|"+ref.SHA256] = struct{}{}
		}
	}
	if hasProducerEmbedded {
		for _, field := range producerFields {
			artifactType := artifactTypeForIngestField(field)
			if artifactType == "" {
				continue
			}
			for rowIndex, digest := range embeddedDigestsForField(ingest, field) {
				key := artifactType + "|" + digest
				if _, ok := refKeys[key]; !ok {
					errs = append(errs, fmt.Sprintf(
						"%s[%d]: missing artifact_refs entry for %s digest %s",
						field, rowIndex, artifactType, digest,
					))
				}
			}
		}
	}
	return joinSemanticErrors(errs)
}

func joinSemanticErrors(errs []string) error {
	if len(errs) == 0 {
		return nil
	}
	return fmt.Errorf("%s", strings.Join(errs, "; "))
}

func validateBenchmarkArtifactRefSemantics(ref PCSBenchmarkArtifactRef) error {
	if ref.ArtifactType == "" {
		return fmt.Errorf("artifact_type is required")
	}
	if _, ok := ingestEmbeddedArrayTypes[ref.ArtifactType]; !ok {
		return fmt.Errorf("unsupported artifact_type %q", ref.ArtifactType)
	}
	if strings.TrimSpace(ref.Path) == "" {
		return fmt.Errorf("path must be non-empty")
	}
	if !strings.HasPrefix(ref.SHA256, "sha256:") {
		return fmt.Errorf("sha256 must be a sha256: hex digest")
	}
	return nil
}

func embeddedIngestObjects(ingest PCSBenchIngestV0, artifactType string) []string {
	var digests []string
	appendDigest := func(d string) {
		if d != "" {
			digests = append(digests, d)
		}
	}
	switch artifactType {
	case "BenchmarkRun.v0":
		for _, row := range ingest.BenchmarkRuns {
			appendDigest(row.SignatureOrDigest)
		}
	case "CoverageReport.v0":
		for _, row := range ingest.CoverageReports {
			appendDigest(row.SignatureOrDigest)
		}
	case "FailureLocalizationResult.v0":
		for _, row := range ingest.FailureLocalizationReports {
			appendDigest(row.SignatureOrDigest)
		}
	case "ExplainQualityReport.v0":
		for _, row := range ingest.ExplainQualityReports {
			appendDigest(row.SignatureOrDigest)
		}
	case "ProfileCoverageReport.v0":
		for _, row := range ingest.ProfileCoverageReports {
			appendDigest(row.SignatureOrDigest)
		}
	}
	return digests
}

func digestMatchesEmbedded(sha256 string, embedded []string) bool {
	for _, d := range embedded {
		if d == sha256 {
			return true
		}
	}
	return false
}

func artifactTypeForIngestField(field string) string {
	for artifactType, fname := range ingestEmbeddedArrayTypes {
		if fname == field {
			return artifactType
		}
	}
	return ""
}

func embeddedDigestsForField(ingest PCSBenchIngestV0, field string) []string {
	artifactType := artifactTypeForIngestField(field)
	return embeddedIngestObjects(ingest, artifactType)
}
