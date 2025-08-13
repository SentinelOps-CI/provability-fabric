// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package sdk

import (
	"time"
)

// Trace represents a complete execution trace
type Trace struct {
	ID        string                 `json:"id"`
	Timestamp time.Time              `json:"timestamp"`
	Subject   Subject                `json:"subject"`
	Steps     []Step                 `json:"steps"`
	Metadata  map[string]interface{} `json:"metadata"`
}

// Subject represents the entity executing the trace
type Subject struct {
	ID           string            `json:"id"`
	Type         SubjectType       `json:"type"`
	Capabilities []string          `json:"capabilities"`
	Labels       map[string]string `json:"labels"`
}

// SubjectType represents the type of subject
type SubjectType string

const (
	SubjectTypeUser     SubjectType = "user"
	SubjectTypeService  SubjectType = "service"
	SubjectTypeEnclave  SubjectType = "enclave"
	SubjectTypeExternal SubjectType = "external"
)

// Step represents a single step in the trace
type Step struct {
	ID        string                 `json:"id"`
	Tool      string                 `json:"tool"`
	Input     interface{}            `json:"input"`
	Output    interface{}            `json:"output"`
	Timestamp time.Time              `json:"timestamp"`
	Duration  time.Duration          `json:"duration"`
	Success   bool                   `json:"success"`
	Error     string                 `json:"error,omitempty"`
	Metadata  map[string]interface{} `json:"metadata,omitempty"`
}

// VerificationResult represents the result of trace verification
type VerificationResult struct {
	Valid      bool        `json:"valid"`
	Trace      *Trace      `json:"trace"`
	Violations []Violation `json:"violations"`
	Timestamp  time.Time   `json:"timestamp"`
}

// Violation represents a policy violation
type Violation struct {
	Type     ViolationType          `json:"type"`
	Severity ViolationSeverity      `json:"severity"`
	Message  string                 `json:"message"`
	StepID   string                 `json:"step_id,omitempty"`
	Details  map[string]interface{} `json:"details,omitempty"`
}

// ViolationType represents the type of violation
type ViolationType string

const (
	ViolationTypeCapabilityMismatch   ViolationType = "capability_mismatch"
	ViolationTypeLabelViolation       ViolationType = "label_violation"
	ViolationTypePolicyViolation      ViolationType = "policy_violation"
	ViolationTypeTimeout              ViolationType = "timeout"
	ViolationTypeAuthenticationFailed ViolationType = "authentication_failed"
)

// ViolationSeverity represents the severity of a violation
type ViolationSeverity string

const (
	ViolationSeverityLow      ViolationSeverity = "low"
	ViolationSeverityMedium   ViolationSeverity = "medium"
	ViolationSeverityHigh     ViolationSeverity = "high"
	ViolationSeverityCritical ViolationSeverity = "critical"
)
