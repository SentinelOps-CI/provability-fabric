// Package policykernel provides an optimized policy kernel with protobuf structs
// and memory pool optimizations for high-performance policy evaluation.
package policykernel

import (
	"fmt"
	"sync"
	"time"
)

// OptimizedKernel represents the optimized policy kernel with protobuf structs
type OptimizedKernel struct {
	config       KernelConfig
	cache        *OptimizedDecisionCache
	pfKeyPair    *PFSignatureKeyPair
	cacheEnabled bool
	
	// Memory pools for efficient allocation
	planPool       *sync.Pool
	stepPool       *sync.Pool
	decisionPool   *sync.Pool
	validationPool *sync.Pool
	
	// Pre-validated policy functions
	policyFunctions map[string]PolicyFunction
	policyCache     *PolicyCache
	
	// Performance profiling
	profiler *PerformanceProfiler
}

// PolicyFunction represents a pre-validated policy function
type PolicyFunction struct {
	Name       string
	Function   func(*Plan, *Step) bool
	Pure       bool // Function has no side effects
	Cacheable  bool // Function result can be cached
	Complexity int  // Function complexity score
}

// PolicyCache provides caching for policy function results
type PolicyCache struct {
	cache map[string]interface{}
	mu    sync.RWMutex
}

// NewOptimizedKernel creates a new optimized policy kernel
func NewOptimizedKernel(config KernelConfig) *OptimizedKernel {
	kernel := &OptimizedKernel{
		config:       config,
		cacheEnabled: config.CacheEnabled,
		policyFunctions: make(map[string]PolicyFunction),
		policyCache: &PolicyCache{
			cache: make(map[string]interface{}),
		},
		profiler: NewPerformanceProfiler(),
	}

	// Initialize memory pools
	kernel.planPool = &sync.Pool{
		New: func() interface{} {
			return &Plan{}
		},
	}
	
	kernel.stepPool = &sync.Pool{
		New: func() interface{} {
			return &Step{}
		},
	}
	
	kernel.decisionPool = &sync.Pool{
		New: func() interface{} {
			return &Decision{}
		},
	}
	
	kernel.validationPool = &sync.Pool{
		New: func() interface{} {
			return &ValidationResult{}
		},
	}

	// Initialize cache if enabled
	if config.CacheEnabled {
		kernel.cache = NewOptimizedDecisionCache(config.CacheMaxSize, config.CacheTTL, config.RedisAddr)
		
		// Generate PF signature key pair
		var err error
		kernel.pfKeyPair, err = NewPFSignatureKeyPair()
		if err != nil {
			kernel.cacheEnabled = false
		}
	}

	// Register pre-validated policy functions
	kernel.registerPolicyFunctions()

	return kernel
}

// registerPolicyFunctions registers all policy functions with pre-validation
func (k *OptimizedKernel) registerPolicyFunctions() {
	// Budget validation function
	k.policyFunctions["budget"] = PolicyFunction{
		Name: "budget",
		Function: func(plan *Plan, step *Step) bool {
			return plan.Constraints.Budget >= 0
		},
		Pure:      true,
		Cacheable: true,
		Complexity: 1,
	}

	// PII validation function
	k.policyFunctions["pii"] = PolicyFunction{
		Name: "pii",
		Function: func(plan *Plan, step *Step) bool {
			return !plan.Constraints.PII || k.hasPIIPermission(&plan.Subject)
		},
		Pure:      true,
		Cacheable: true,
		Complexity: 2,
	}

	// Capability validation function
	k.policyFunctions["capability"] = PolicyFunction{
		Name: "capability",
		Function: func(plan *Plan, step *Step) bool {
			return k.hasRequiredCapabilities(&plan.Subject, step.CapsRequired)
		},
		Pure:      true,
		Cacheable: true,
		Complexity: 3,
	}

	// Tenant validation function
	k.policyFunctions["tenant"] = PolicyFunction{
		Name: "tenant",
		Function: func(plan *Plan, step *Step) bool {
			return k.isValidTenant(plan.Tenant)
		},
		Pure:      true,
		Cacheable: true,
		Complexity: 1,
	}

	// Expiration validation function
	k.policyFunctions["expiration"] = PolicyFunction{
		Name: "expiration",
		Function: func(plan *Plan, step *Step) bool {
			return time.Now().Before(plan.ExpiresAt)
		},
		Pure:      true,
		Cacheable: true,
		Complexity: 1,
	}
}

// ValidatePlan validates a plan using optimized protobuf structs and pre-validated functions
func (k *OptimizedKernel) ValidatePlan(plan *Plan) *ValidationResult {
	start := time.Now()
	defer func() {
		k.profiler.RecordOperation("ValidatePlan", time.Since(start))
	}()

	// Get validation result from pool
	result := k.validationPool.Get().(*ValidationResult)
	result.Valid = true
	result.Errors = result.Errors[:0]
	result.Warnings = result.Warnings[:0]

	// Execute pre-validated policy functions
	for name, policyFunc := range k.policyFunctions {
		if !policyFunc.Function(plan, nil) {
			result.Valid = false
			result.Errors = append(result.Errors, fmt.Sprintf("Policy function %s failed", name))
		}
	}

	// Validate steps
	for i, step := range plan.Steps {
		if !k.validateStep(plan, &step) {
			result.Valid = false
			result.Errors = append(result.Errors, fmt.Sprintf("Step %d validation failed", i))
		}
	}

	// Return result to pool
	k.validationPool.Put(result)
	return result
}

// validateStep validates a single step using optimized validation
func (k *OptimizedKernel) validateStep(plan *Plan, step *Step) bool {
	// Check capability requirements
	if !k.hasRequiredCapabilities(&plan.Subject, step.CapsRequired) {
		return false
	}

	// Check PII constraints
	if plan.Constraints.PII && !k.hasPIIPermission(&plan.Subject) {
		return false
	}

	return true
}

// ApprovePlan approves a plan using optimized processing
func (k *OptimizedKernel) ApprovePlan(plan *Plan) *Decision {
	start := time.Now()
	defer func() {
		k.profiler.RecordOperation("ApprovePlan", time.Since(start))
	}()

	// Get decision from pool
	decision := k.decisionPool.Get().(*Decision)
	decision.ApprovedSteps = decision.ApprovedSteps[:0]
	decision.Valid = false
	decision.Reason = ""
	decision.Errors = decision.Errors[:0]
	decision.Warnings = decision.Warnings[:0]

	// Check cache first
	if k.cacheEnabled {
		if cached := k.cache.Get(plan.PlanID); cached != nil {
			// Return cached decision to pool
			k.decisionPool.Put(decision)
			return cached
		}
	}

	// Validate plan
	validation := k.ValidatePlan(plan)
	if !validation.Valid {
		decision.Reason = "Plan validation failed"
		decision.Errors = validation.Errors
		decision.Warnings = validation.Warnings
		
		// Return decision to pool
		k.decisionPool.Put(decision)
		return decision
	}

	// Process steps
	approvedSteps := make([]ApprovedStep, 0, len(plan.Steps))
	for i, step := range plan.Steps {
		if k.approveStep(plan, &step) {
			approvedStep := ApprovedStep{
				StepIndex: i,
				Tool:      step.Tool,
				Args:      step.Args,
				Receipts:  step.Receipts,
			}
			approvedSteps = append(approvedSteps, approvedStep)
		}
	}

	decision.ApprovedSteps = approvedSteps
	decision.Valid = true
	decision.Reason = "Plan approved"

	// Cache decision if enabled
	if k.cacheEnabled {
		k.cache.Set(plan.PlanID, decision)
	}

	// Return decision to pool
	k.decisionPool.Put(decision)
	return decision
}

// approveStep approves a single step
func (k *OptimizedKernel) approveStep(plan *Plan, step *Step) bool {
	// Check capability requirements
	if !k.hasRequiredCapabilities(&plan.Subject, step.CapsRequired) {
		return false
	}

	// Check PII constraints
	if plan.Constraints.PII && !k.hasPIIPermission(&plan.Subject) {
		return false
	}

	return true
}

// hasRequiredCapabilities checks if subject has required capabilities
func (k *OptimizedKernel) hasRequiredCapabilities(subject *Subject, required []string) bool {
	if len(required) == 0 {
		return true
	}

	subjectCaps := make(map[string]bool)
	for _, cap := range subject.Caps {
		subjectCaps[cap] = true
	}

	for _, requiredCap := range required {
		if !subjectCaps[requiredCap] {
			return false
		}
	}

	return true
}

// hasPIIPermission checks if subject has PII permission
func (k *OptimizedKernel) hasPIIPermission(subject *Subject) bool {
	// Check for PII-specific capabilities
	for _, cap := range subject.Caps {
		if cap == "pii_access" || cap == "data_analyst" || cap == "admin" {
			return true
		}
	}
	return false
}

// isValidTenant checks if tenant is valid
func (k *OptimizedKernel) isValidTenant(tenant string) bool {
	if len(k.config.AllowedTenants) == 0 {
		return true
	}

	for _, allowed := range k.config.AllowedTenants {
		if allowed == tenant {
			return true
		}
	}
	return false
}

// GetPerformanceProfile returns performance profiling data
func (k *OptimizedKernel) GetPerformanceProfile() *PerformanceProfile {
	return k.profiler.GetProfile()
}

// OptimizedDecisionCache provides optimized caching for decisions
type OptimizedDecisionCache struct {
	cache    map[string]*Decision
	mu       sync.RWMutex
	maxSize  int
	ttl      time.Duration
	redisAddr string
}

// NewOptimizedDecisionCache creates a new optimized decision cache
func NewOptimizedDecisionCache(maxSize int, ttl time.Duration, redisAddr string) *OptimizedDecisionCache {
	cache := &OptimizedDecisionCache{
		cache:     make(map[string]*Decision),
		maxSize:   maxSize,
		ttl:       ttl,
		redisAddr: redisAddr,
	}

	// Start cleanup goroutine
	go cache.cleanup()

	return cache
}

// Get retrieves a decision from cache
func (c *OptimizedDecisionCache) Get(planID string) *Decision {
	c.mu.RLock()
	defer c.mu.RUnlock()

	if decision, exists := c.cache[planID]; exists {
		return decision
	}

	return nil
}

// Set stores a decision in cache
func (c *OptimizedDecisionCache) Set(planID string, decision *Decision) {
	c.mu.Lock()
	defer c.mu.Unlock()

	// Check cache size
	if len(c.cache) >= c.maxSize {
		// Remove oldest entry (simple FIFO for now)
		for key := range c.cache {
			delete(c.cache, key)
			break
		}
	}

	c.cache[planID] = decision
}

// cleanup removes expired entries from cache
func (c *OptimizedDecisionCache) cleanup() {
	ticker := time.NewTicker(c.ttl)
	defer ticker.Stop()

	for range ticker.C {
		c.mu.Lock()
		// Clear all entries (simple implementation)
		c.cache = make(map[string]*Decision)
		c.mu.Unlock()
	}
}

// PerformanceProfiler provides performance profiling for the kernel
type PerformanceProfiler struct {
	operations map[string]*OperationStats
	mu         sync.RWMutex
}

// OperationStats tracks performance statistics for operations
type OperationStats struct {
	Count       int64
	TotalTime   time.Duration
	MinTime     time.Duration
	MaxTime     time.Duration
	LastUpdated time.Time
}

// NewPerformanceProfiler creates a new performance profiler
func NewPerformanceProfiler() *PerformanceProfiler {
	return &PerformanceProfiler{
		operations: make(map[string]*OperationStats),
	}
}

// RecordOperation records the execution time of an operation
func (p *PerformanceProfiler) RecordOperation(name string, duration time.Duration) {
	p.mu.Lock()
	defer p.mu.Unlock()

	stats, exists := p.operations[name]
	if !exists {
		stats = &OperationStats{
			MinTime: duration,
			MaxTime: duration,
		}
		p.operations[name] = stats
	}

	stats.Count++
	stats.TotalTime += duration
	if duration < stats.MinTime {
		stats.MinTime = duration
	}
	if duration > stats.MaxTime {
		stats.MaxTime = duration
	}
	stats.LastUpdated = time.Now()
}

// GetProfile returns the current performance profile
func (p *PerformanceProfiler) GetProfile() *PerformanceProfile {
	p.mu.RLock()
	defer p.mu.RUnlock()

	profile := &PerformanceProfile{
		Operations: make(map[string]*OperationProfile),
	}

	for name, stats := range p.operations {
		if stats.Count > 0 {
			profile.Operations[name] = &OperationProfile{
				Count:        stats.Count,
				AverageTime:  stats.TotalTime.Nanoseconds() / stats.Count,
				MinTime:      stats.MinTime.Nanoseconds(),
				MaxTime:      stats.MaxTime.Nanoseconds(),
				LastUpdated:  stats.LastUpdated,
			}
		}
	}

	return profile
}

// PerformanceProfile represents the overall performance profile
type PerformanceProfile struct {
	Operations map[string]*OperationProfile
}

// OperationProfile represents performance profile for a single operation
type OperationProfile struct {
	Count       int64
	AverageTime int64
	MinTime     int64
	MaxTime     int64
	LastUpdated time.Time
}
