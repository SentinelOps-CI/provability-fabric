// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

// SemanticVersion represents a semantic version
type SemanticVersion struct {
	Major      int
	Minor      int
	Patch      int
	PreRelease string
	Build      string
}

// VersionConstraint represents a version constraint
type VersionConstraint struct {
	Operator string // "=", ">", ">=", "<", "<=", "~", "^"
	Version  SemanticVersion
}

// ParseSemanticVersion parses a version string into SemanticVersion
func ParseSemanticVersion(version string) (*SemanticVersion, error) {
	// Regex for semantic versioning: https://semver.org/
	re := regexp.MustCompile(`^(\d+)\.(\d+)\.(\d+)(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?(?:\+([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?$`)

	matches := re.FindStringSubmatch(version)
	if matches == nil {
		return nil, fmt.Errorf("invalid semantic version format: %s", version)
	}

	major, _ := strconv.Atoi(matches[1])
	minor, _ := strconv.Atoi(matches[2])
	patch, _ := strconv.Atoi(matches[3])
	preRelease := matches[4]
	build := matches[5]

	return &SemanticVersion{
		Major:      major,
		Minor:      minor,
		Patch:      patch,
		PreRelease: preRelease,
		Build:      build,
	}, nil
}

// String returns the string representation of the version
func (v *SemanticVersion) String() string {
	version := fmt.Sprintf("%d.%d.%d", v.Major, v.Minor, v.Patch)
	if v.PreRelease != "" {
		version += "-" + v.PreRelease
	}
	if v.Build != "" {
		version += "+" + v.Build
	}
	return version
}

// Compare compares two semantic versions
// Returns: -1 if v < other, 0 if v == other, 1 if v > other
func (v *SemanticVersion) Compare(other *SemanticVersion) int {
	// Compare major, minor, patch
	if v.Major != other.Major {
		return compareInt(v.Major, other.Major)
	}
	if v.Minor != other.Minor {
		return compareInt(v.Minor, other.Minor)
	}
	if v.Patch != other.Patch {
		return compareInt(v.Patch, other.Patch)
	}

	// Pre-release versions have lower precedence
	if v.PreRelease == "" && other.PreRelease != "" {
		return 1
	}
	if v.PreRelease != "" && other.PreRelease == "" {
		return -1
	}
	if v.PreRelease != "" && other.PreRelease != "" {
		return comparePreRelease(v.PreRelease, other.PreRelease)
	}

	return 0
}

// compareInt compares two integers
func compareInt(a, b int) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
}

// comparePreRelease compares pre-release identifiers
func comparePreRelease(a, b string) int {
	identifiersA := strings.Split(a, ".")
	identifiersB := strings.Split(b, ".")

	maxLen := len(identifiersA)
	if len(identifiersB) > maxLen {
		maxLen = len(identifiersB)
	}

	for i := 0; i < maxLen; i++ {
		var idA, idB string
		if i < len(identifiersA) {
			idA = identifiersA[i]
		}
		if i < len(identifiersB) {
			idB = identifiersB[i]
		}

		// Numeric identifiers have lower precedence than non-numeric
		numA, isNumA := strconv.Atoi(idA)
		numB, isNumB := strconv.Atoi(idB)

		if isNumA == nil && isNumB == nil {
			// Both numeric
			if numA != numB {
				return compareInt(numA, numB)
			}
		} else if isNumA == nil {
			// A is numeric, B is not
			return -1
		} else if isNumB == nil {
			// B is numeric, A is not
			return 1
		} else {
			// Both non-numeric, compare as strings
			if idA != idB {
				if idA < idB {
					return -1
				}
				return 1
			}
		}
	}

	return 0
}

// Satisfies checks if a version satisfies a constraint
func (v *SemanticVersion) Satisfies(constraint VersionConstraint) bool {
	comparison := v.Compare(&constraint.Version)

	switch constraint.Operator {
	case "=":
		return comparison == 0
	case ">":
		return comparison > 0
	case ">=":
		return comparison >= 0
	case "<":
		return comparison < 0
	case "<=":
		return comparison <= 0
	case "~":
		// Compatible with: same major, minor, patch >= constraint
		return v.Major == constraint.Version.Major &&
			v.Minor == constraint.Version.Minor &&
			v.Patch >= constraint.Version.Patch
	case "^":
		// Compatible with: same major, version >= constraint
		return v.Major == constraint.Version.Major &&
			v.Compare(&constraint.Version) >= 0
	default:
		return false
	}
}

// ParseVersionConstraint parses a version constraint string
func ParseVersionConstraint(constraint string) (*VersionConstraint, error) {
	// Regex for version constraints
	re := regexp.MustCompile(`^(=|>|>=|<|<=|~|\^)?(.+)$`)
	matches := re.FindStringSubmatch(constraint)
	if matches == nil {
		return nil, fmt.Errorf("invalid version constraint format: %s", constraint)
	}

	operator := matches[1]
	if operator == "" {
		operator = "="
	}

	versionStr := matches[2]
	version, err := ParseSemanticVersion(versionStr)
	if err != nil {
		return nil, fmt.Errorf("invalid version in constraint: %w", err)
	}

	return &VersionConstraint{
		Operator: operator,
		Version:  *version,
	}, nil
}

// VersionRange represents a range of versions
type VersionRange struct {
	Constraints []VersionConstraint
}

// ParseVersionRange parses a version range string
func ParseVersionRange(rangeStr string) (*VersionRange, error) {
	// Support for ranges like ">=1.0.0 <2.0.0"
	constraints := strings.Fields(rangeStr)
	var versionConstraints []VersionConstraint

	for _, constraint := range constraints {
		parsed, err := ParseVersionConstraint(constraint)
		if err != nil {
			return nil, fmt.Errorf("invalid constraint '%s': %w", constraint, err)
		}
		versionConstraints = append(versionConstraints, *parsed)
	}

	return &VersionRange{
		Constraints: versionConstraints,
	}, nil
}

// Satisfies checks if a version satisfies all constraints in the range
func (r *VersionRange) Satisfies(version *SemanticVersion) bool {
	for _, constraint := range r.Constraints {
		if !version.Satisfies(constraint) {
			return false
		}
	}
	return true
}

// FindLatestCompatibleVersion finds the latest version that satisfies the constraint
func FindLatestCompatibleVersion(versions []string, constraint string) (string, error) {
	parsedConstraint, err := ParseVersionConstraint(constraint)
	if err != nil {
		return "", fmt.Errorf("invalid constraint: %w", err)
	}

	var compatibleVersions []*SemanticVersion
	for _, versionStr := range versions {
		version, err := ParseSemanticVersion(versionStr)
		if err != nil {
			continue // Skip invalid versions
		}

		if version.Satisfies(*parsedConstraint) {
			compatibleVersions = append(compatibleVersions, version)
		}
	}

	if len(compatibleVersions) == 0 {
		return "", fmt.Errorf("no compatible versions found for constraint: %s", constraint)
	}

	// Find the latest version
	latest := compatibleVersions[0]
	for _, version := range compatibleVersions[1:] {
		if version.Compare(latest) > 0 {
			latest = version
		}
	}

	return latest.String(), nil
}

// ValidateVersionFormat validates if a version string follows semantic versioning
func ValidateVersionFormat(version string) error {
	_, err := ParseSemanticVersion(version)
	return err
}

// IsBreakingChange checks if upgrading from oldVersion to newVersion is a breaking change
func IsBreakingChange(oldVersion, newVersion string) (bool, error) {
	old, err := ParseSemanticVersion(oldVersion)
	if err != nil {
		return false, fmt.Errorf("invalid old version: %w", err)
	}

	new, err := ParseSemanticVersion(newVersion)
	if err != nil {
		return false, fmt.Errorf("invalid new version: %w", err)
	}

	// Major version change is always breaking
	if new.Major > old.Major {
		return true, nil
	}

	// Major version decrease is also breaking
	if new.Major < old.Major {
		return true, nil
	}

	return false, nil
}

// GetUpgradeType determines the type of upgrade between two versions
func GetUpgradeType(oldVersion, newVersion string) (string, error) {
	old, err := ParseSemanticVersion(oldVersion)
	if err != nil {
		return "", fmt.Errorf("invalid old version: %w", err)
	}

	new, err := ParseSemanticVersion(newVersion)
	if err != nil {
		return "", fmt.Errorf("invalid new version: %w", err)
	}

	if new.Major > old.Major {
		return "major", nil
	}
	if new.Minor > old.Minor {
		return "minor", nil
	}
	if new.Patch > old.Patch {
		return "patch", nil
	}
	if new.Compare(old) < 0 {
		return "downgrade", nil
	}
	return "none", nil
}
