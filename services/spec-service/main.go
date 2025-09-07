// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"regexp"
	"strings"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

// PolicyCompileRequest represents a request to compile English to ActionDSL
type PolicyCompileRequest struct {
	English  string            `json:"english" binding:"required"`
	Metadata map[string]string `json:"metadata,omitempty"`
	PolicyID string            `json:"policy_id,omitempty"`
	Version  string            `json:"version,omitempty"`
}

// PolicyCompileResponse represents the compilation result
type PolicyCompileResponse struct {
	ActionDSL   ActionDSLPolicy `json:"actionDsl"`
	Diagnostics []Diagnostic    `json:"diagnostics"`
	PolicyHash  string          `json:"policy_hash"`
	Timestamp   time.Time       `json:"timestamp"`
	IR          JSONIR          `json:"ir"`
}

// SourceMapEntry maps a DSL rule to its source line
type SourceMapEntry struct {
	RuleID   string `json:"rule_id"`
	Line     int    `json:"line"`
	Original string `json:"original"`
}

// JSONIR is a simplified intermediate representation with source mappings
type JSONIR struct {
	PolicyID  string           `json:"policy_id"`
	Version   string           `json:"version"`
	SourceMap []SourceMapEntry `json:"source_map"`
}

// ActionDSLPolicy represents the compiled policy
type ActionDSLPolicy struct {
	PolicyID    string            `json:"policy_id"`
	Version     string            `json:"version"`
	Rules       []DSLRule         `json:"rules"`
	Metadata    map[string]string `json:"metadata"`
	Permissions []Permission      `json:"permissions"`
}

// DSLRule represents a policy rule in ActionDSL
type DSLRule struct {
	RuleID    string     `json:"rule_id"`
	Type      string     `json:"type"` // "allow" | "forbid" | "rate_limit" | "budget"
	Role      string     `json:"role,omitempty"`
	Action    Action     `json:"action,omitempty"`
	Guard     ABACExpr   `json:"guard,omitempty"`
	RateLimit *RateLimit `json:"rate_limit,omitempty"`
	Budget    *Budget    `json:"budget,omitempty"`
}

// Action represents an action in the DSL
type Action struct {
	Type      string   `json:"type"` // "call" | "read" | "write" | "log" | "declassify" | "emit"
	Tool      string   `json:"tool,omitempty"`
	Args      []string `json:"args,omitempty"`
	Doc       string   `json:"doc,omitempty"`
	Path      []string `json:"path,omitempty"`
	Message   string   `json:"message,omitempty"`
	FromLabel string   `json:"from_label,omitempty"`
	ToLabel   string   `json:"to_label,omitempty"`
	Event     string   `json:"event,omitempty"`
	Data      string   `json:"data,omitempty"`
}

// ABACExpr represents ABAC expressions
type ABACExpr struct {
	Type   string    `json:"type"` // "attr" | "session" | "epoch_in" | "scope" | "and" | "or" | "not" | "true" | "false"
	Key    string    `json:"key,omitempty"`
	Value  string    `json:"value,omitempty"`
	Start  *int      `json:"start,omitempty"`
	End    *int      `json:"end,omitempty"`
	Tenant string    `json:"tenant,omitempty"`
	Left   *ABACExpr `json:"left,omitempty"`
	Right  *ABACExpr `json:"right,omitempty"`
	Expr   *ABACExpr `json:"expr,omitempty"`
}

// Permission represents a permission in the policy
type Permission struct {
	Principal  string   `json:"principal"`
	Actions    []string `json:"actions"`
	Resources  []string `json:"resources"`
	Conditions ABACExpr `json:"conditions"`
}

// RateLimit represents rate limiting configuration
type RateLimit struct {
	Key           string `json:"key"`
	WindowMs      int    `json:"window_ms"`
	MaxOperations int    `json:"max_operations"`
}

// Budget represents budget constraints
type Budget struct {
	MaxCost  float64 `json:"max_cost"`
	Currency string  `json:"currency"`
}

// Diagnostic represents compilation diagnostics
type Diagnostic struct {
	Level   string `json:"level"` // "error" | "warning" | "info"
	Message string `json:"message"`
	Line    int    `json:"line,omitempty"`
	Column  int    `json:"column,omitempty"`
	Code    string `json:"code,omitempty"`
}

// SpecService provides English to ActionDSL conversion
type SpecService struct {
	policies map[string]ActionDSLPolicy
}

// NewSpecService creates a new spec service instance
func NewSpecService() *SpecService {
	return &SpecService{
		policies: make(map[string]ActionDSLPolicy),
	}
}

// CompilePolicy converts English policy to ActionDSL
func (s *SpecService) CompilePolicy(ctx context.Context, req PolicyCompileRequest) (*PolicyCompileResponse, error) {
	// Generate policy ID if not provided
	if req.PolicyID == "" {
		req.PolicyID = uuid.New().String()
	}

	if req.Version == "" {
		req.Version = "1.0.0"
	}

	// Parse English policy using NLP patterns
	actionDSL, diagnostics, sourceMap := s.parseEnglishPolicy(req.English, req.PolicyID, req.Version, req.Metadata)

	// Calculate policy hash
	policyHash := s.calculatePolicyHash(actionDSL)

	// Store policy
	s.policies[req.PolicyID] = actionDSL

	return &PolicyCompileResponse{
		ActionDSL:   actionDSL,
		Diagnostics: diagnostics,
		PolicyHash:  policyHash,
		Timestamp:   time.Now(),
		IR: JSONIR{
			PolicyID:  req.PolicyID,
			Version:   req.Version,
			SourceMap: sourceMap,
		},
	}, nil
}

// parseEnglishPolicy converts English text to ActionDSL using pattern matching
func (s *SpecService) parseEnglishPolicy(english, policyID, version string, metadata map[string]string) (ActionDSLPolicy, []Diagnostic, []SourceMapEntry) {
	var diagnostics []Diagnostic
	var rules []DSLRule
	var permissions []Permission
	var sourceMap []SourceMapEntry

	// Normalize text
	trimmed := strings.TrimSpace(english)
	rawLines := strings.Split(trimmed, "\n")
	lowerLines := make([]string, len(rawLines))
	for i, rl := range rawLines {
		lowerLines[i] = strings.ToLower(strings.TrimSpace(rl))
	}

	ruleCounter := 0

	for lineNum := range lowerLines {
		line := strings.TrimSpace(lowerLines[lineNum])
		raw := strings.TrimSpace(rawLines[lineNum])
		if line == "" {
			continue
		}

		// Parse different rule patterns
		if rule, diagnostic := s.parseAllowRule(line, lineNum, &ruleCounter); rule != nil {
			rules = append(rules, *rule)
			if diagnostic != nil {
				diagnostics = append(diagnostics, *diagnostic)
			}
			sourceMap = append(sourceMap, SourceMapEntry{RuleID: rule.RuleID, Line: lineNum + 1, Original: raw})
		} else if rule, diagnostic := s.parseForbidRule(line, lineNum, &ruleCounter); rule != nil {
			rules = append(rules, *rule)
			if diagnostic != nil {
				diagnostics = append(diagnostics, *diagnostic)
			}
			sourceMap = append(sourceMap, SourceMapEntry{RuleID: rule.RuleID, Line: lineNum + 1, Original: raw})
		} else if rule, diagnostic := s.parseRateLimitRule(line, lineNum, &ruleCounter); rule != nil {
			rules = append(rules, *rule)
			if diagnostic != nil {
				diagnostics = append(diagnostics, *diagnostic)
			}
			sourceMap = append(sourceMap, SourceMapEntry{RuleID: rule.RuleID, Line: lineNum + 1, Original: raw})
		} else if rule, diagnostic := s.parseBudgetRule(line, lineNum, &ruleCounter); rule != nil {
			rules = append(rules, *rule)
			if diagnostic != nil {
				diagnostics = append(diagnostics, *diagnostic)
			}
			sourceMap = append(sourceMap, SourceMapEntry{RuleID: rule.RuleID, Line: lineNum + 1, Original: raw})
		} else {
			// Unrecognized pattern
			diagnostics = append(diagnostics, Diagnostic{
				Level:   "warning",
				Message: fmt.Sprintf("Unrecognized policy pattern: %s", line),
				Line:    lineNum + 1,
			})
			// Ambiguity hint for who/which/when
			if strings.Contains(line, " who ") || strings.Contains(line, " which ") || strings.Contains(line, " when ") {
				diagnostics = append(diagnostics, Diagnostic{
					Level:   "warning",
					Code:    "SPEC_AMBIGUOUS_ACTOR",
					Message: "Ambiguous actor reference (who/which/when). Specify an explicit role or principal.",
					Line:    lineNum + 1,
				})
			}
		}
	}

	// Add default metadata
	if metadata == nil {
		metadata = make(map[string]string)
	}
	metadata["compiled_at"] = time.Now().Format(time.RFC3339)
	metadata["compiler_version"] = "spec-service-v1.0.0"

	return ActionDSLPolicy{
		PolicyID:    policyID,
		Version:     version,
		Rules:       rules,
		Metadata:    metadata,
		Permissions: permissions,
	}, diagnostics, sourceMap
}

// parseAllowRule parses allow patterns
func (s *SpecService) parseAllowRule(line string, lineNum int, counter *int) (*DSLRule, *Diagnostic) {
	// Pattern: "allow <role> to <action> <resource> when <condition>"
	// Pattern: "only <role> may <action> <resource>"
	// Pattern: "<service> may call <endpoint>"

	allowPatterns := []string{
		`allow\s+(\w+)\s+to\s+(\w+)\s+(.+?)\s+when\s+(.+)`,
		`only\s+(\w+)\s+may\s+(\w+)\s+(.+)`,
		`(\w+)\s+may\s+call\s+(.+)`,
		`(\w+)\s+can\s+(\w+)\s+(.+)`,
	}

	for _, pattern := range allowPatterns {
		re := regexp.MustCompile(pattern)
		matches := re.FindStringSubmatch(line)

		if len(matches) > 2 {
			*counter++

			role := matches[1]
			action := s.parseAction(matches[2], matches[3:])
			guard := s.parseGuard(matches[len(matches)-1])

			var diag *Diagnostic
			// Emit ambiguity warning if role is pronoun-like
			if role == "who" || role == "which" || role == "when" {
				d := Diagnostic{
					Level:   "warning",
					Code:    "SPEC_AMBIGUOUS_ACTOR",
					Message: "Ambiguous actor '" + role + "' — specify an explicit role or principal",
					Line:    lineNum + 1,
				}
				diag = &d
			}

			return &DSLRule{
				RuleID: fmt.Sprintf("rule_%d", *counter),
				Type:   "allow",
				Role:   role,
				Action: action,
				Guard:  guard,
			}, diag
		}
	}

	return nil, nil
}

// parseForbidRule parses forbid patterns
func (s *SpecService) parseForbidRule(line string, lineNum int, counter *int) (*DSLRule, *Diagnostic) {
	// Pattern: "forbid <role> from <action> <resource>"
	// Pattern: "block <action> for <role>"
	// Pattern: "deny <role> access to <resource>"

	forbidPatterns := []string{
		`forbid\s+(\w+)\s+from\s+(\w+)\s+(.+)`,
		`block\s+(\w+)\s+for\s+(\w+)`,
		`deny\s+(\w+)\s+access\s+to\s+(.+)`,
		`(\w+)\s+cannot\s+(\w+)\s+(.+)`,
	}

	for _, pattern := range forbidPatterns {
		re := regexp.MustCompile(pattern)
		matches := re.FindStringSubmatch(line)

		if len(matches) > 2 {
			*counter++

			role := matches[1]
			action := s.parseAction(matches[2], matches[3:])
			guard := ABACExpr{Type: "true"} // Default guard

			var diag *Diagnostic
			if role == "who" || role == "which" || role == "when" {
				d := Diagnostic{
					Level:   "warning",
					Code:    "SPEC_AMBIGUOUS_ACTOR",
					Message: "Ambiguous actor '" + role + "' — specify an explicit role or principal",
					Line:    lineNum + 1,
				}
				diag = &d
			}

			return &DSLRule{
				RuleID: fmt.Sprintf("rule_%d", *counter),
				Type:   "forbid",
				Role:   role,
				Action: action,
				Guard:  guard,
			}, diag
		}
	}

	return nil, nil
}

// parseRateLimitRule parses rate limit patterns
func (s *SpecService) parseRateLimitRule(line string, lineNum int, counter *int) (*DSLRule, *Diagnostic) {
	// Pattern: "rate limit <key> to <max> per <window>"
	// Pattern: "limit <key> to <max> operations per <window>"

	rateLimitPatterns := []string{
		`rate\s+limit\s+(\w+)\s+to\s+(\d+)\s+per\s+(\d+)\s*(\w+)`,
		`limit\s+(\w+)\s+to\s+(\d+)\s+operations\s+per\s+(\d+)\s*(\w+)`,
		`(\w+)\s+limited\s+to\s+(\d+)\s+per\s+(\d+)\s*(\w+)`,
	}

	for _, pattern := range rateLimitPatterns {
		re := regexp.MustCompile(pattern)
		matches := re.FindStringSubmatch(line)

		if len(matches) >= 4 {
			*counter++

			key := matches[1]
			maxOps := s.parseInt(matches[2], 100)
			window := s.parseInt(matches[3], 1000)
			unit := matches[4]

			// Convert time units to milliseconds
			windowMs := s.convertToMs(window, unit)

			return &DSLRule{
				RuleID: fmt.Sprintf("rule_%d", *counter),
				Type:   "rate_limit",
				RateLimit: &RateLimit{
					Key:           key,
					WindowMs:      windowMs,
					MaxOperations: maxOps,
				},
			}, nil
		}
	}

	return nil, nil
}

// parseBudgetRule parses budget constraint patterns
func (s *SpecService) parseBudgetRule(line string, lineNum int, counter *int) (*DSLRule, *Diagnostic) {
	// Pattern: "budget limit <amount> <currency>"
	// Pattern: "maximum cost <amount> <currency>"

	budgetPatterns := []string{
		`budget\s+limit\s+(\d+(?:\.\d+)?)\s+(\w+)`,
		`maximum\s+cost\s+(\d+(?:\.\d+)?)\s+(\w+)`,
		`limit\s+spending\s+to\s+(\d+(?:\.\d+)?)\s+(\w+)`,
	}

	for _, pattern := range budgetPatterns {
		re := regexp.MustCompile(pattern)
		matches := re.FindStringSubmatch(line)

		if len(matches) >= 3 {
			*counter++

			amount := s.parseFloat(matches[1], 1000.0)
			currency := matches[2]

			return &DSLRule{
				RuleID: fmt.Sprintf("rule_%d", *counter),
				Type:   "budget",
				Budget: &Budget{
					MaxCost:  amount,
					Currency: currency,
				},
			}, nil
		}
	}

	return nil, nil
}

// parseAction extracts action information from text
func (s *SpecService) parseAction(actionText string, resources []string) Action {
	actionText = strings.ToLower(strings.TrimSpace(actionText))

	// Determine action type
	if strings.Contains(actionText, "call") {
		tool := s.extractTool(actionText, resources)
		return Action{
			Type: "call",
			Tool: tool,
			Args: resources,
		}
	} else if strings.Contains(actionText, "read") {
		doc, path := s.extractDocAndPath(resources)
		return Action{
			Type: "read",
			Doc:  doc,
			Path: path,
		}
	} else if strings.Contains(actionText, "write") {
		doc, path := s.extractDocAndPath(resources)
		return Action{
			Type: "write",
			Doc:  doc,
			Path: path,
		}
	} else if strings.Contains(actionText, "log") {
		return Action{
			Type:    "log",
			Message: strings.Join(resources, " "),
		}
	}

	// Default to call action
	return Action{
		Type: "call",
		Tool: actionText,
		Args: resources,
	}
}

// parseGuard parses guard conditions into ABAC expressions
func (s *SpecService) parseGuard(guardText string) ABACExpr {
	if guardText == "" {
		return ABACExpr{Type: "true"}
	}

	guardText = strings.ToLower(strings.TrimSpace(guardText))

	// Parse different guard patterns
	if strings.Contains(guardText, "and") {
		parts := strings.Split(guardText, " and ")
		if len(parts) == 2 {
			left := s.parseSimpleGuard(parts[0])
			right := s.parseSimpleGuard(parts[1])
			return ABACExpr{
				Type:  "and",
				Left:  &left,
				Right: &right,
			}
		}
	}

	if strings.Contains(guardText, "or") {
		parts := strings.Split(guardText, " or ")
		if len(parts) == 2 {
			left := s.parseSimpleGuard(parts[0])
			right := s.parseSimpleGuard(parts[1])
			return ABACExpr{
				Type:  "or",
				Left:  &left,
				Right: &right,
			}
		}
	}

	return s.parseSimpleGuard(guardText)
}

// parseSimpleGuard parses simple guard expressions
func (s *SpecService) parseSimpleGuard(guardText string) ABACExpr {
	guardText = strings.TrimSpace(guardText)

	// Pattern: "role is <value>"
	if re := regexp.MustCompile(`role\s+is\s+(\w+)`); re.MatchString(guardText) {
		matches := re.FindStringSubmatch(guardText)
		return ABACExpr{
			Type:  "attr",
			Key:   "role",
			Value: matches[1],
		}
	}

	// Pattern: "tenant is <value>"
	if re := regexp.MustCompile(`tenant\s+is\s+(\w+)`); re.MatchString(guardText) {
		matches := re.FindStringSubmatch(guardText)
		return ABACExpr{
			Type:   "scope",
			Tenant: matches[1],
		}
	}

	// Pattern: "session <key> is <value>"
	if re := regexp.MustCompile(`session\s+(\w+)\s+is\s+(\w+)`); re.MatchString(guardText) {
		matches := re.FindStringSubmatch(guardText)
		return ABACExpr{
			Type:  "session",
			Key:   matches[1],
			Value: matches[2],
		}
	}

	// Pattern: "epoch between <start> and <end>"
	if re := regexp.MustCompile(`epoch\s+between\s+(\d+)\s+and\s+(\d+)`); re.MatchString(guardText) {
		matches := re.FindStringSubmatch(guardText)
		start := s.parseInt(matches[1], 0)
		end := s.parseInt(matches[2], 999999)
		return ABACExpr{
			Type:  "epoch_in",
			Start: &start,
			End:   &end,
		}
	}

	// Default to true
	return ABACExpr{Type: "true"}
}

// Helper functions
func (s *SpecService) extractTool(actionText string, resources []string) string {
	if len(resources) > 0 {
		return resources[0]
	}

	// Extract tool name from action text
	words := strings.Fields(actionText)
	for _, word := range words {
		if !s.isStopWord(word) {
			return word
		}
	}

	return "unknown"
}

func (s *SpecService) extractDocAndPath(resources []string) (string, []string) {
	if len(resources) == 0 {
		return "unknown", []string{}
	}

	doc := resources[0]
	path := resources[1:]

	return doc, path
}

func (s *SpecService) isStopWord(word string) bool {
	stopWords := []string{"to", "from", "the", "a", "an", "and", "or", "but", "in", "on", "at", "by", "for", "with", "without"}
	for _, stopWord := range stopWords {
		if word == stopWord {
			return true
		}
	}
	return false
}

func (s *SpecService) parseInt(str string, defaultVal int) int {
	// Simple integer parsing with default
	var val int
	if _, err := fmt.Sscanf(str, "%d", &val); err != nil {
		return defaultVal
	}
	return val
}

func (s *SpecService) parseFloat(str string, defaultVal float64) float64 {
	// Simple float parsing with default
	var val float64
	if _, err := fmt.Sscanf(str, "%f", &val); err != nil {
		return defaultVal
	}
	return val
}

func (s *SpecService) convertToMs(value int, unit string) int {
	switch unit {
	case "s", "sec", "second", "seconds":
		return value * 1000
	case "m", "min", "minute", "minutes":
		return value * 60 * 1000
	case "h", "hour", "hours":
		return value * 60 * 60 * 1000
	default:
		return value // Assume milliseconds
	}
}

func (s *SpecService) calculatePolicyHash(policy ActionDSLPolicy) string {
	// Create deterministic hash of policy
	data, _ := json.Marshal(policy)
	return fmt.Sprintf("%x", data)[:64] // Simplified hash
}

// HTTP handlers
func (s *SpecService) compileHandler(c *gin.Context) {
	var req PolicyCompileRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}

	resp, err := s.CompilePolicy(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}

	c.JSON(http.StatusOK, resp)
}

func (s *SpecService) getPolicyHandler(c *gin.Context) {
	policyID := c.Param("id")

	policy, exists := s.policies[policyID]
	if !exists {
		c.JSON(http.StatusNotFound, gin.H{"error": "Policy not found"})
		return
	}

	c.JSON(http.StatusOK, policy)
}

func (s *SpecService) listPoliciesHandler(c *gin.Context) {
	var policies []ActionDSLPolicy
	for _, policy := range s.policies {
		policies = append(policies, policy)
	}

	c.JSON(http.StatusOK, gin.H{
		"policies": policies,
		"count":    len(policies),
	})
}

func (s *SpecService) healthHandler(c *gin.Context) {
	c.JSON(http.StatusOK, gin.H{
		"status":    "healthy",
		"service":   "spec-service",
		"version":   "1.0.0",
		"timestamp": time.Now(),
		"policies":  len(s.policies),
	})
}

func main() {
	// Initialize service
	service := NewSpecService()

	// Set up Gin router
	r := gin.Default()

	// CORS middleware
	r.Use(func(c *gin.Context) {
		c.Header("Access-Control-Allow-Origin", "*")
		c.Header("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
		c.Header("Access-Control-Allow-Headers", "Content-Type, Authorization")

		if c.Request.Method == "OPTIONS" {
			c.AbortWithStatus(http.StatusOK)
			return
		}

		c.Next()
	})

	// API routes
	v1 := r.Group("/api/v1")
	{
		v1.POST("/policy/compile", service.compileHandler)
		v1.GET("/policy/:id", service.getPolicyHandler)
		v1.GET("/policies", service.listPoliciesHandler)
		v1.GET("/health", service.healthHandler)
	}

	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8001"
	}

	log.Printf("Spec Service starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}
