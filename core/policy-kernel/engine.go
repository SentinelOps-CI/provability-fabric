package policykernel

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"time"
)

// Plan represents a typed plan with capabilities and constraints
type Plan struct {
	PlanID           string      `json:"plan_id"`
	Tenant           string      `json:"tenant"`
	Subject          Subject     `json:"subject"`
	Steps            []Step      `json:"steps"`
	Constraints      Constraints `json:"constraints"`
	SystemPromptHash string      `json:"system_prompt_hash"`
	CreatedAt        time.Time   `json:"created_at"`
	ExpiresAt        time.Time   `json:"expires_at"`
}

// Subject represents the entity executing the plan
type Subject struct {
	ID   string   `json:"id"`
	Caps []string `json:"caps"`
}

// Step represents a single action in the plan
type Step struct {
	Tool         string                 `json:"tool"`
	Args         map[string]interface{} `json:"args"`
	CapsRequired []string               `json:"caps_required"`
	LabelsIn     []string               `json:"labels_in"`
	LabelsOut    []string               `json:"labels_out"`
}

// Constraints represents plan-level constraints
type Constraints struct {
	Budget     float64 `json:"budget"`
	PII        bool    `json:"pii"`
	DPEpsilon  float64 `json:"dp_epsilon"`
	DPDelta    float64 `json:"dp_delta,omitempty"`
	LatencyMax float64 `json:"latency_max,omitempty"`
}

// ValidationResult represents the result of plan validation
type ValidationResult struct {
	Valid    bool     `json:"valid"`
	Errors   []string `json:"errors,omitempty"`
	Warnings []string `json:"warnings,omitempty"`
}

// Kernel represents the policy kernel
type Kernel struct {
	config KernelConfig
}

// KernelConfig represents kernel configuration
type KernelConfig struct {
	MaxBudget      float64
	MaxEpsilon     float64
	MaxLatency     float64
	AllowedTenants []string
}

// NewKernel creates a new policy kernel
func NewKernel(config KernelConfig) *Kernel {
	return &Kernel{config: config}
}

// ValidatePlan validates a plan against all policy rules
func (k *Kernel) ValidatePlan(plan *Plan) ValidationResult {
	result := ValidationResult{Valid: true}

	// Check plan expiration
	if time.Now().After(plan.ExpiresAt) {
		result.Valid = false
		result.Errors = append(result.Errors, "Plan has expired")
	}

	// Validate tenant
	if !k.isValidTenant(plan.Tenant) {
		result.Valid = false
		result.Errors = append(result.Errors, "Invalid tenant")
	}

	// Validate system prompt hash
	if !k.isValidHash(plan.SystemPromptHash) {
		result.Valid = false
		result.Errors = append(result.Errors, "Invalid system prompt hash")
	}

	// Validate constraints
	if constraintErrors := k.validateConstraints(plan.Constraints); len(constraintErrors) > 0 {
		result.Valid = false
		result.Errors = append(result.Errors, constraintErrors...)
	}

	// Validate each step
	for i, step := range plan.Steps {
		if stepErrors := k.validateStep(plan.Subject, step, i); len(stepErrors) > 0 {
			result.Valid = false
			result.Errors = append(result.Errors, stepErrors...)
		}
	}

	// Validate label flow
	if flowErrors := k.validateLabelFlow(plan.Steps); len(flowErrors) > 0 {
		result.Valid = false
		result.Errors = append(result.Errors, flowErrors...)
	}

	return result
}

// validateConstraints validates plan-level constraints
func (k *Kernel) validateConstraints(constraints Constraints) []string {
	var errors []string

	if constraints.Budget > k.config.MaxBudget {
		errors = append(errors, fmt.Sprintf("Budget %f exceeds maximum %f", constraints.Budget, k.config.MaxBudget))
	}

	if constraints.DPEpsilon > k.config.MaxEpsilon {
		errors = append(errors, fmt.Sprintf("DP epsilon %f exceeds maximum %f", constraints.DPEpsilon, k.config.MaxEpsilon))
	}

	if constraints.LatencyMax > k.config.MaxLatency {
		errors = append(errors, fmt.Sprintf("Latency %f exceeds maximum %f", constraints.LatencyMax, k.config.MaxLatency))
	}

	return errors
}

// validateStep validates a single step
func (k *Kernel) validateStep(subject Subject, step Step, stepIndex int) []string {
	var errors []string

	// Check capability match
	for _, requiredCap := range step.CapsRequired {
		if !k.hasCapability(subject.Caps, requiredCap) {
			errors = append(errors, fmt.Sprintf("Step %d: missing required capability '%s'", stepIndex, requiredCap))
		}
	}

	// Validate tool name
	if step.Tool == "" {
		errors = append(errors, fmt.Sprintf("Step %d: tool name is required", stepIndex))
	}

	// Validate arguments
	if step.Args == nil {
		errors = append(errors, fmt.Sprintf("Step %d: arguments are required", stepIndex))
	}

	return errors
}

// validateLabelFlow validates that label flow is consistent
func (k *Kernel) validateLabelFlow(steps []Step) []string {
	var errors []string
	availableLabels := make(map[string]bool)

	// Initialize with empty set
	availableLabels[""] = true

	for i, step := range steps {
		// Check that input labels are available
		for _, labelIn := range step.LabelsIn {
			if !availableLabels[labelIn] {
				errors = append(errors, fmt.Sprintf("Step %d: input label '%s' not available", i, labelIn))
			}
		}

		// Add output labels to available set
		for _, labelOut := range step.LabelsOut {
			availableLabels[labelOut] = true
		}
	}

	return errors
}

// hasCapability checks if subject has a specific capability
func (k *Kernel) hasCapability(subjectCaps []string, requiredCap string) bool {
	for _, cap := range subjectCaps {
		if cap == requiredCap {
			return true
		}
	}
	return false
}

// isValidTenant checks if tenant is allowed
func (k *Kernel) isValidTenant(tenant string) bool {
	for _, allowedTenant := range k.config.AllowedTenants {
		if allowedTenant == tenant {
			return true
		}
	}
	return false
}

// isValidHash validates SHA-256 hash format
func (k *Kernel) isValidHash(hash string) bool {
	if len(hash) != 64 {
		return false
	}
	_, err := hex.DecodeString(hash)
	return err == nil
}

// HashSystemPrompt creates a SHA-256 hash of the system prompt
func HashSystemPrompt(prompt string) string {
	hash := sha256.Sum256([]byte(prompt))
	return hex.EncodeToString(hash[:])
}

// LoadPlanFromJSON loads a plan from JSON
func LoadPlanFromJSON(data []byte) (*Plan, error) {
	var plan Plan
	if err := json.Unmarshal(data, &plan); err != nil {
		return nil, fmt.Errorf("failed to unmarshal plan: %w", err)
	}
	return &plan, nil
}

// SavePlanToJSON saves a plan to JSON
func (p *Plan) SavePlanToJSON() ([]byte, error) {
	return json.MarshalIndent(p, "", "  ")
}
