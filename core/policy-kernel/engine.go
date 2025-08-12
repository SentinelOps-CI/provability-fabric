package policykernel

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"strings"
	"time"
)

// InputChannels represents the classification of input channels
type InputChannels struct {
	System    SystemChannel      `json:"system"`
	User      UserChannel        `json:"user"`
	Retrieved []RetrievedChannel `json:"retrieved,omitempty"`
	File      []FileChannel      `json:"file,omitempty"`
}

// SystemChannel represents trusted system input
type SystemChannel struct {
	Hash       string `json:"hash"`
	PolicyHash string `json:"policy_hash"`
}

// UserChannel represents untrusted user input
type UserChannel struct {
	ContentHash string `json:"content_hash"`
	Quoted      bool   `json:"quoted"`
}

// RetrievedChannel represents untrusted retrieved content
type RetrievedChannel struct {
	ReceiptID   string   `json:"receipt_id"`
	ContentHash string   `json:"content_hash"`
	Quoted      bool     `json:"quoted"`
	Labels      []string `json:"labels"`
}

// FileChannel represents untrusted file content
type FileChannel struct {
	SHA256    string `json:"sha256"`
	MediaType string `json:"media_type"`
	Quoted    bool   `json:"quoted"`
}

// AccessReceipt represents a signed access receipt
type AccessReceipt struct {
	ReceiptID  string `json:"receipt_id"`
	Tenant     string `json:"tenant"`
	SubjectID  string `json:"subject_id"`
	QueryHash  string `json:"query_hash"`
	IndexShard string `json:"index_shard"`
	Timestamp  int64  `json:"timestamp"`
	ResultHash string `json:"result_hash"`
	SignAlg    string `json:"sign_alg"`
	Sig        string `json:"sig"`
}

// Plan represents a typed plan with capabilities and constraints
type Plan struct {
	PlanID            string        `json:"plan_id"`
	Tenant            string        `json:"tenant"`
	Subject           Subject       `json:"subject"`
	InputChannels     InputChannels `json:"input_channels"`
	Steps             []Step        `json:"steps"`
	Constraints       Constraints   `json:"constraints"`
	SystemPromptHash  string        `json:"system_prompt_hash"`
	AllowedOperations []string      `json:"allowed_operations"`
	CreatedAt         time.Time     `json:"created_at"`
	ExpiresAt         time.Time     `json:"expires_at"`
	SecurityLevel     string        `json:"security_level,omitempty"`
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
	Receipts     []AccessReceipt        `json:"receipts,omitempty"`
}

// Constraints represents plan-level constraints
type Constraints struct {
	Budget              float64 `json:"budget"`
	PII                 bool    `json:"pii"`
	DPEpsilon           float64 `json:"dp_epsilon"`
	DPDelta             float64 `json:"dp_delta,omitempty"`
	LatencyMax          float64 `json:"latency_max,omitempty"`
	MaxTokens           int     `json:"max_tokens,omitempty"`
	MaxRetrievalResults int     `json:"max_retrieval_results,omitempty"`
}

// Decision represents the kernel's decision on plan execution
type Decision struct {
	ApprovedSteps  []ApprovedStep       `json:"approved_steps"`
	Reason         string               `json:"reason"`
	Valid          bool                 `json:"valid"`
	Errors         []string             `json:"errors,omitempty"`
	Warnings       []string             `json:"warnings,omitempty"`
	ReasonCodes    []string             `json:"reason_codes,omitempty"`
	SecurityChecks SecurityCheckResults `json:"security_checks"`
}

// SecurityCheckResults tracks the three core security checks
type SecurityCheckResults struct {
	CapabilityMatch      bool     `json:"capability_match"`
	ReceiptValidation    bool     `json:"receipt_validation"`
	LabelFlowRefinements bool     `json:"label_flow_refinements"`
	InjectionProtection  bool     `json:"injection_protection"`
	Details              []string `json:"details,omitempty"`
}

// ApprovedStep represents a step that has been approved for execution
type ApprovedStep struct {
	StepIndex int                    `json:"step_index"`
	Tool      string                 `json:"tool"`
	Args      map[string]interface{} `json:"args"`
	Receipts  []AccessReceipt        `json:"receipts,omitempty"`
}

// ValidationResult represents the result of plan validation
type ValidationResult struct {
	Valid    bool     `json:"valid"`
	Errors   []string `json:"errors,omitempty"`
	Warnings []string `json:"warnings,omitempty"`
}

// Kernel represents the policy kernel
type Kernel struct {
	config       KernelConfig
	cache        *DecisionCache
	pfKeyPair    *PFSignatureKeyPair
	cacheEnabled bool
}

// KernelConfig represents kernel configuration
type KernelConfig struct {
	MaxBudget           float64
	MaxEpsilon          float64
	MaxLatency          float64
	MaxTokens           int
	MaxRetrievalResults int
	AllowedTenants      []string
	StrictKernel        bool          // New flag for strict kernel checks
	CacheEnabled        bool          // Enable fast-path decision caching
	CacheMaxSize        int           // Maximum number of cached decisions
	CacheTTL            time.Duration // TTL for cached decisions
	RedisAddr           string        // Redis address for distributed caching
}

// NewKernel creates a new policy kernel
func NewKernel(config KernelConfig) *Kernel {
	// Default to strict mode if not specified
	if !config.StrictKernel {
		config.StrictKernel = true
	}

	// Set default cache values if not specified
	if config.CacheMaxSize == 0 {
		config.CacheMaxSize = 10000 // Default to 10k cached decisions
	}
	if config.CacheTTL == 0 {
		config.CacheTTL = 60 * time.Second // Default to 60s TTL
	}

	kernel := &Kernel{
		config:       config,
		cacheEnabled: config.CacheEnabled,
	}

	// Initialize cache if enabled
	if config.CacheEnabled {
		kernel.cache = NewDecisionCache(config.CacheMaxSize, config.CacheTTL, config.RedisAddr)

		// Generate PF signature key pair
		var err error
		kernel.pfKeyPair, err = NewPFSignatureKeyPair()
		if err != nil {
			// Log error but continue without PF signatures
			// In production, this should be a fatal error
			kernel.cacheEnabled = false
		}
	}

	return kernel
}

// ValidatePlan validates a plan against all policy rules
func (k *Kernel) ValidatePlan(plan *Plan) ValidationResult {
	result := ValidationResult{Valid: true}

	// Check plan expiration
	if time.Now().After(plan.ExpiresAt) {
		result.Valid = false
		result.Errors = append(result.Errors, "PLAN_EXPIRED: Plan has expired")
	}

	// Validate tenant
	if !k.isValidTenant(plan.Tenant) {
		result.Valid = false
		result.Errors = append(result.Errors, "INVALID_TENANT: Invalid tenant")
	}

	// Validate system prompt hash
	if !k.isValidHash(plan.SystemPromptHash) {
		result.Valid = false
		result.Errors = append(result.Errors, "INVALID_SYSTEM_HASH: Invalid system prompt hash")
	}

	// Validate allowed operations
	if opErrors := k.validateAllowedOperations(plan.AllowedOperations, plan.Steps); len(opErrors) > 0 {
		result.Valid = false
		result.Errors = append(result.Errors, opErrors...)
	}

	// Validate input channels
	if channelErrors := k.validateInputChannels(plan.InputChannels, plan.SystemPromptHash); len(channelErrors) > 0 {
		result.Valid = false
		result.Errors = append(result.Errors, channelErrors...)
	}

	// Validate constraints
	if constraintErrors := k.validateConstraints(plan.Constraints); len(constraintErrors) > 0 {
		result.Valid = false
		result.Errors = append(result.Errors, constraintErrors...)
	}

	// STRICT KERNEL CHECKS - All three must pass
	if k.config.StrictKernel {
		// 1. Capability Match Check
		if capErrors := k.validateCapabilityMatch(plan.Subject, plan.Steps); len(capErrors) > 0 {
			result.Valid = false
			result.Errors = append(result.Errors, capErrors...)
		}

		// 2. Receipt Presence Check
		if receiptErrors := k.validateReceiptPresence(plan.Steps); len(receiptErrors) > 0 {
			result.Valid = false
			result.Errors = append(result.Errors, receiptErrors...)
		}

		// 3. Label Flow + Numeric Refinements Check
		if labelErrors := k.validateLabelFlowAndRefinements(plan.Steps, plan.Constraints); len(labelErrors) > 0 {
			result.Valid = false
			result.Errors = append(result.Errors, labelErrors...)
		}
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

// ValidatePlanWithCache validates a plan with fast-path caching
func (k *Kernel) ValidatePlanWithCache(plan *Plan, capsTokenID string) (*Decision, *PFSignature, error) {
	// Check if cache is enabled
	if !k.cacheEnabled || k.cache == nil {
		// Fall back to normal validation
		validation := k.ValidatePlan(plan)
		if !validation.Valid {
			return nil, nil, fmt.Errorf("plan validation failed: %v", validation.Errors)
		}

		decision := k.ApprovePlan(plan)
		return &decision, nil, nil
	}

	// Create cache key
	cacheKey := CacheKey{
		PlanHash:    plan.PlanID, // Using PlanID as hash for now
		CapsTokenID: capsTokenID,
		PolicyHash:  plan.InputChannels.System.PolicyHash,
	}

	// Try to get from cache first
	if cached, exists := k.cache.Get(cacheKey); exists {
		// Return cached decision with PF signature
		pfSig, err := k.pfKeyPair.SignDecision(cacheKey, cacheKey.PolicyHash, k.config.CacheTTL)
		if err != nil {
			// Log error but continue with cached decision
			return cached, nil, nil
		}
		return cached, pfSig, nil
	}

	// Not in cache, perform full validation
	validation := k.ValidatePlan(plan)
	if !validation.Valid {
		return nil, nil, fmt.Errorf("plan validation failed: %v", validation.Errors)
	}

	// Approve the plan
	decision := k.ApprovePlan(plan)

	// Cache the decision
	if err := k.cache.Set(cacheKey, decision); err != nil {
		// Log error but continue
		// In production, this should be logged
	}

	// Generate PF signature
	pfSig, err := k.pfKeyPair.SignDecision(cacheKey, cacheKey.PolicyHash, k.config.CacheTTL)
	if err != nil {
		// Log error but continue without signature
		return &decision, nil, nil
	}

	return &decision, pfSig, nil
}

// ApprovePlan returns a Decision with approved steps for execution
func (k *Kernel) ApprovePlan(plan *Plan) Decision {
	decision := Decision{
		Valid:  true,
		Reason: "Plan approved for execution",
		SecurityChecks: SecurityCheckResults{
			CapabilityMatch:      true,
			ReceiptValidation:    true,
			LabelFlowRefinements: true,
			InjectionProtection:  true,
		},
	}

	// First validate the plan
	validation := k.ValidatePlan(plan)
	if !validation.Valid {
		decision.Valid = false
		decision.Reason = "Plan validation failed"
		decision.Errors = validation.Errors
		decision.Warnings = validation.Warnings

		// Extract reason codes from errors
		decision.ReasonCodes = k.extractReasonCodes(validation.Errors)

		// Update security check results based on errors
		decision.SecurityChecks = k.updateSecurityCheckResults(validation.Errors)

		return decision
	}

	// Approve each step that passes validation
	for i, step := range plan.Steps {
		approvedStep := ApprovedStep{
			StepIndex: i,
			Tool:      step.Tool,
			Args:      step.Args,
			Receipts:  step.Receipts,
		}
		decision.ApprovedSteps = append(decision.ApprovedSteps, approvedStep)
	}

	return decision
}

// validateAllowedOperations ensures all steps use only allowed operations
func (k *Kernel) validateAllowedOperations(allowedOps []string, steps []Step) []string {
	var errors []string

	if len(allowedOps) == 0 {
		return []string{"ALLOWED_OPS_MISSING: Plan must specify allowed operations"}
	}

	for i, step := range steps {
		allowed := false
		for _, allowedOp := range allowedOps {
			if step.Tool == allowedOp {
				allowed = true
				break
			}
		}
		if !allowed {
			errors = append(errors, fmt.Sprintf("OPERATION_NOT_ALLOWED: Step %d tool '%s' not in allowed operations list", i, step.Tool))
		}
	}

	return errors
}

// InvalidateCacheByPolicy invalidates all cached decisions for a specific policy
func (k *Kernel) InvalidateCacheByPolicy(policyHash string) error {
	if k.cacheEnabled && k.cache != nil {
		return k.cache.InvalidateByPolicyHash(policyHash)
	}
	return nil
}

// GetCacheStats returns cache performance statistics
func (k *Kernel) GetCacheStats() *CacheStats {
	if k.cacheEnabled && k.cache != nil {
		stats := k.cache.GetStats()
		return &stats
	}
	return nil
}

// Close cleans up the kernel and its cache
func (k *Kernel) Close() error {
	if k.cacheEnabled && k.cache != nil {
		return k.cache.Close()
	}
	return nil
}

// validateConstraints validates plan-level constraints
func (k *Kernel) validateConstraints(constraints Constraints) []string {
	var errors []string

	if constraints.Budget > k.config.MaxBudget {
		errors = append(errors, fmt.Sprintf("BUDGET_EXCEEDED: Budget %f exceeds maximum %f", constraints.Budget, k.config.MaxBudget))
	}

	if constraints.DPEpsilon > k.config.MaxEpsilon {
		errors = append(errors, fmt.Sprintf("EPSILON_EXCEEDED: DP epsilon %f exceeds maximum %f", constraints.DPEpsilon, k.config.MaxEpsilon))
	}

	if constraints.LatencyMax > k.config.MaxLatency {
		errors = append(errors, fmt.Sprintf("LATENCY_EXCEEDED: Latency %f exceeds maximum %f", constraints.LatencyMax, k.config.MaxLatency))
	}

	if constraints.MaxTokens > k.config.MaxTokens {
		errors = append(errors, fmt.Sprintf("TOKENS_EXCEEDED: Max tokens %d exceeds maximum %d", constraints.MaxTokens, k.config.MaxTokens))
	}

	if constraints.MaxRetrievalResults > k.config.MaxRetrievalResults {
		errors = append(errors, fmt.Sprintf("RETRIEVAL_RESULTS_EXCEEDED: Max retrieval results %d exceeds maximum %d", constraints.MaxRetrievalResults, k.config.MaxRetrievalResults))
	}

	return errors
}

// validateInputChannels validates input channel classification and quoting requirements
func (k *Kernel) validateInputChannels(channels InputChannels, systemPromptHash string) []string {
	var errors []string

	// Validate system channel (trusted)
	if !k.isValidHash(channels.System.Hash) {
		errors = append(errors, "INVALID_SYSTEM_HASH: Invalid system channel hash")
	}
	if !k.isValidHash(channels.System.PolicyHash) {
		errors = append(errors, "INVALID_POLICY_HASH: Invalid system policy hash")
	}

	// System hash must match the plan's system prompt hash
	if channels.System.Hash != systemPromptHash {
		errors = append(errors, "SYSTEM_HASH_MISMATCH: System channel hash does not match plan system prompt hash")
	}

	// Validate user channel (untrusted) - STRICT: quoted=true required
	if !k.isValidHash(channels.User.ContentHash) {
		errors = append(errors, "INVALID_USER_HASH: Invalid user content hash")
	}
	if !channels.User.Quoted {
		errors = append(errors, "UNTRUSTED_NOT_QUOTED: User input must be quoted (quoted=true) - injection protection required")
	}

	// Validate retrieved channels (untrusted) - STRICT: quoted=true required
	for i, retrieved := range channels.Retrieved {
		if !k.isValidHash(retrieved.ContentHash) {
			errors = append(errors, fmt.Sprintf("INVALID_RETRIEVED_HASH: Invalid retrieved content hash at index %d", i))
		}
		if !retrieved.Quoted {
			errors = append(errors, fmt.Sprintf("UNTRUSTED_NOT_QUOTED: Retrieved content at index %d must be quoted (quoted=true) - injection protection required", i))
		}
		if retrieved.ReceiptID == "" {
			errors = append(errors, fmt.Sprintf("RECEIPT_MISSING: Retrieved content at index %d must have receipt_id", i))
		}
		if len(retrieved.Labels) == 0 {
			errors = append(errors, fmt.Sprintf("LABELS_MISSING: Retrieved content at index %d must have labels", i))
		}
	}

	// Validate file channels (untrusted) - STRICT: quoted=true required
	for i, file := range channels.File {
		if !k.isValidHash(file.SHA256) {
			errors = append(errors, fmt.Sprintf("INVALID_FILE_HASH: Invalid file SHA256 at index %d", i))
		}
		if !file.Quoted {
			errors = append(errors, fmt.Sprintf("UNTRUSTED_NOT_QUOTED: File content at index %d must be quoted (quoted=true) - injection protection required", i))
		}
		if file.MediaType == "" {
			errors = append(errors, fmt.Sprintf("MEDIA_TYPE_MISSING: File content at index %d must have media_type", i))
		}
	}

	return errors
}

// validateStep validates a single step
func (k *Kernel) validateStep(subject Subject, step Step, stepIndex int) []string {
	var errors []string

	// Check capability match
	for _, requiredCap := range step.CapsRequired {
		if !k.hasCapability(subject.Caps, requiredCap) {
			errors = append(errors, fmt.Sprintf("CAP_MISS: Step %d: missing required capability '%s'", stepIndex, requiredCap))
		}
	}

	// Validate tool name
	if step.Tool == "" {
		errors = append(errors, fmt.Sprintf("TOOL_MISSING: Step %d: tool name is required", stepIndex))
	}

	// Validate arguments
	if step.Args == nil {
		errors = append(errors, fmt.Sprintf("ARGS_MISSING: Step %d: arguments are required", stepIndex))
	}

	// Validate receipts for retrieval steps
	if step.Tool == "retrieval" || step.Tool == "search" {
		if len(step.Receipts) == 0 {
			errors = append(errors, fmt.Sprintf("RECEIPT_MISSING: Step %d: retrieval step requires access receipts", stepIndex))
		} else {
			// Verify each receipt
			for i, receipt := range step.Receipts {
				if receiptErr := k.verifyReceipt(receipt); receiptErr != nil {
					errors = append(errors, fmt.Sprintf("RECEIPT_INVALID: Step %d: receipt %d verification failed: %s", stepIndex, i, receiptErr.Error()))
				}
			}
		}
	}

	return errors
}

// verifyReceipt verifies a signed access receipt
func (k *Kernel) verifyReceipt(receipt AccessReceipt) error {
	// Basic validation
	if receipt.ReceiptID == "" {
		return fmt.Errorf("receipt ID is required")
	}
	if receipt.Tenant == "" {
		return fmt.Errorf("receipt tenant is required")
	}
	if receipt.IndexShard == "" {
		return fmt.Errorf("receipt index shard is required")
	}
	if receipt.SignAlg != "ed25519" {
		return fmt.Errorf("unsupported signature algorithm: %s", receipt.SignAlg)
	}
	if receipt.Sig == "" {
		return fmt.Errorf("receipt signature is required")
	}

	// TODO: Implement actual signature verification
	// This would require access to the public keys for each shard
	// For now, we'll do basic structural validation

	return nil
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
				errors = append(errors, fmt.Sprintf("LABEL_FLOW: Step %d: input label '%s' not available", i, labelIn))
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

// STRICT KERNEL CHECK 1: Capability Match
// validateCapabilityMatch ensures caps_required ⊆ subject.caps
func (k *Kernel) validateCapabilityMatch(subject Subject, steps []Step) []string {
	var errors []string

	for i, step := range steps {
		for _, requiredCap := range step.CapsRequired {
			if !k.hasCapability(subject.Caps, requiredCap) {
				errors = append(errors, fmt.Sprintf("CAP_MISS: Step %d: subject lacks capability '%s'", i, requiredCap))
			}
		}
	}

	return errors
}

// STRICT KERNEL CHECK 2: Receipt Presence
// validateReceiptPresence ensures every read step has a verified Access Receipt
func (k *Kernel) validateReceiptPresence(steps []Step) []string {
	var errors []string

	for i, step := range steps {
		// Check if this step requires data access (read operations)
		if k.isReadOperation(step.Tool) {
			if len(step.Receipts) == 0 {
				errors = append(errors, fmt.Sprintf("RECEIPT_MISSING: Step %d: read operation requires access receipt", i))
				continue
			}

			// Verify each receipt
			for j, receipt := range step.Receipts {
				if err := k.verifyReceipt(receipt); err != nil {
					errors = append(errors, fmt.Sprintf("RECEIPT_INVALID: Step %d, Receipt %d: %v", i, j, err))
				}
			}
		}
	}

	return errors
}

// STRICT KERNEL CHECK 3: Label Flow + Numeric Refinements
// validateLabelFlowAndRefinements ensures labels and budgets are within limits
func (k *Kernel) validateLabelFlowAndRefinements(steps []Step, constraints Constraints) []string {
	var errors []string

	// Check label flow
	for i, step := range steps {
		// Validate input labels
		for _, labelIn := range step.LabelsIn {
			if !k.isValidLabel(labelIn) {
				errors = append(errors, fmt.Sprintf("LABEL_FLOW: Step %d: invalid input label '%s'", i, labelIn))
			}
		}

		// Validate output labels
		for _, labelOut := range step.LabelsOut {
			if !k.isValidLabel(labelOut) {
				errors = append(errors, fmt.Sprintf("LABEL_FLOW: Step %d: invalid output label '%s'", i, labelOut))
			}
		}
	}

	// Check numeric refinements (budgets and epsilon)
	if constraints.Budget > k.config.MaxBudget {
		errors = append(errors, fmt.Sprintf("BUDGET_EXCEEDED: budget %f exceeds maximum %f", constraints.Budget, k.config.MaxBudget))
	}

	if constraints.DPEpsilon > k.config.MaxEpsilon {
		errors = append(errors, fmt.Sprintf("EPSILON_EXCEEDED: epsilon %f exceeds maximum %f", constraints.DPEpsilon, k.config.MaxEpsilon))
	}

	return errors
}

// Helper function to check if operation requires data access
func (k *Kernel) isReadOperation(tool string) bool {
	readTools := []string{"data_query", "retrieve", "search", "fetch", "get"}
	for _, readTool := range readTools {
		if tool == readTool {
			return true
		}
	}
	return false
}

// Helper function to validate label format
func (k *Kernel) isValidLabel(label string) bool {
	// Basic label validation - can be extended
	if label == "" {
		return false
	}
	if len(label) > 100 {
		return false
	}
	// Check for valid label format (key:value)
	if !strings.Contains(label, ":") {
		return false
	}
	return true
}

// extractReasonCodes extracts reason codes from error messages
func (k *Kernel) extractReasonCodes(errors []string) []string {
	var codes []string
	for _, err := range errors {
		if strings.Contains(err, ":") {
			parts := strings.SplitN(err, ":", 2)
			if len(parts) > 0 {
				codes = append(codes, strings.TrimSpace(parts[0]))
			}
		}
	}
	return codes
}

// updateSecurityCheckResults updates security check results based on validation errors
func (k *Kernel) updateSecurityCheckResults(errors []string) SecurityCheckResults {
	results := SecurityCheckResults{
		CapabilityMatch:      true,
		ReceiptValidation:    true,
		LabelFlowRefinements: true,
		InjectionProtection:  true,
	}

	for _, err := range errors {
		if strings.Contains(err, "CAP_MISS") {
			results.CapabilityMatch = false
		}
		if strings.Contains(err, "RECEIPT_MISSING") || strings.Contains(err, "RECEIPT_INVALID") {
			results.ReceiptValidation = false
		}
		if strings.Contains(err, "LABEL_FLOW") || strings.Contains(err, "BUDGET_EXCEEDED") || strings.Contains(err, "EPSILON_EXCEEDED") {
			results.LabelFlowRefinements = false
		}
		if strings.Contains(err, "UNTRUSTED_NOT_QUOTED") || strings.Contains(err, "OPERATION_NOT_ALLOWED") {
			results.InjectionProtection = false
		}
	}

	return results
}
