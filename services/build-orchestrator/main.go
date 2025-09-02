// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"context"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

// PolicyBuildRequest represents a request to build a policy
type PolicyBuildRequest struct {
	PolicyHash    string                 `json:"policy_hash" binding:"required"`
	ActionDSL     map[string]interface{} `json:"action_dsl" binding:"required"`
	ProofHash     string                 `json:"proof_hash" binding:"required"`
	Metadata      map[string]string      `json:"metadata,omitempty"`
	SigningKey    string                 `json:"signing_key,omitempty"`
}

// PolicyBuildResponse represents the build result
type PolicyBuildResponse struct {
	BuildID       string            `json:"build_id"`
	DFAHash       string            `json:"dfa_hash"`
	AutomataHash  string            `json:"automata_hash"`
	LabelerHash   string            `json:"labeler_hash"`
	ProofInputs   map[string]interface{} `json:"proof_inputs"`
	Artifacts     []string          `json:"artifacts"`
	Signature     string            `json:"signature,omitempty"`
	Status        string            `json:"status"`
	Timestamp     time.Time         `json:"timestamp"`
	ExecutionTime int               `json:"execution_time_ms"`
}

// DFAState represents a state in the compiled DFA
type DFAState struct {
	StateID     int               `json:"state_id"`
	Name        string            `json:"name"`
	Type        string            `json:"type"` // "initial" | "accept" | "reject" | "intermediate"
	Metadata    map[string]string `json:"metadata,omitempty"`
}

// DFATransition represents a transition in the DFA
type DFATransition struct {
	FromState   int               `json:"from_state"`
	ToState     int               `json:"to_state"`
	Trigger     string            `json:"trigger"`
	Guard       string            `json:"guard,omitempty"`
	Action      string            `json:"action,omitempty"`
	Metadata    map[string]string `json:"metadata,omitempty"`
}

// CompiledDFA represents the complete compiled automata
type CompiledDFA struct {
	States       []DFAState       `json:"states"`
	Transitions  []DFATransition  `json:"transitions"`
	InitialState int              `json:"initial_state"`
	AcceptStates []int            `json:"accept_states"`
	RejectStates []int            `json:"reject_states"`
	Metadata     map[string]string `json:"metadata"`
}

// LabelerConfig represents the IFC labeler configuration
type LabelerConfig struct {
	Labels       []Label           `json:"labels"`
	LabelRules   []LabelRule       `json:"label_rules"`
	FlowPolicies []FlowPolicy      `json:"flow_policies"`
	Metadata     map[string]string `json:"metadata"`
}

// Label represents an information flow label
type Label struct {
	Name        string   `json:"name"`
	Level       int      `json:"level"`
	Categories  []string `json:"categories,omitempty"`
	Tenant      string   `json:"tenant,omitempty"`
}

// LabelRule represents a labeling rule
type LabelRule struct {
	Pattern     string `json:"pattern"`
	Label       string `json:"label"`
	Condition   string `json:"condition,omitempty"`
}

// FlowPolicy represents an information flow policy
type FlowPolicy struct {
	From        string `json:"from"`
	To          string `json:"to"`
	Allowed     bool   `json:"allowed"`
	Condition   string `json:"condition,omitempty"`
}

// PolicyBuild represents a signed policy build
type PolicyBuild struct {
	BuildID      string        `json:"build_id"`
	PolicyHash   string        `json:"policy_hash"`
	ProofHash    string        `json:"proof_hash"`
	DFAHash      string        `json:"dfa_hash"`
	AutomataHash string        `json:"automata_hash"`
	LabelerHash  string        `json:"labeler_hash"`
	CompiledDFA  CompiledDFA   `json:"compiled_dfa"`
	Labeler      LabelerConfig `json:"labeler"`
	Signature    string        `json:"signature"`
	CreatedAt    time.Time     `json:"created_at"`
	Metadata     map[string]string `json:"metadata"`
}

// BuildOrchestrator handles ActionDSL compilation and policy builds
type BuildOrchestrator struct {
	builds    map[string]PolicyBuild
	cachePath string
}

// NewBuildOrchestrator creates a new build orchestrator instance
func NewBuildOrchestrator() *BuildOrchestrator {
	cachePath := os.Getenv("BUILD_CACHE_PATH")
	if cachePath == "" {
		cachePath = "/tmp/build-cache"
	}
	
	// Ensure cache directory exists
	os.MkdirAll(cachePath, 0755)
	
	return &BuildOrchestrator{
		builds:    make(map[string]PolicyBuild),
		cachePath: cachePath,
	}
}

// BuildPolicy compiles ActionDSL to DFA and creates signed policy build
func (s *BuildOrchestrator) BuildPolicy(ctx context.Context, req PolicyBuildRequest) (*PolicyBuildResponse, error) {
	startTime := time.Now()
	buildID := uuid.New().String()
	
	// Compile ActionDSL to DFA
	dfa, err := s.compileActionDSLToDFA(req.ActionDSL)
	if err != nil {
		return nil, fmt.Errorf("DFA compilation failed: %w", err)
	}
	
	// Generate labeler configuration
	labeler := s.generateLabelerConfig(req.ActionDSL)
	
	// Calculate hashes
	dfaHash := s.calculateDFAHash(dfa)
	automataHash := s.calculateAutomataHash(dfa)
	labelerHash := s.calculateLabelerHash(labeler)
	
	// Create policy build
	build := PolicyBuild{
		BuildID:      buildID,
		PolicyHash:   req.PolicyHash,
		ProofHash:    req.ProofHash,
		DFAHash:      dfaHash,
		AutomataHash: automataHash,
		LabelerHash:  labelerHash,
		CompiledDFA:  dfa,
		Labeler:      labeler,
		CreatedAt:    time.Now(),
		Metadata:     req.Metadata,
	}
	
	// Sign the build if signing key provided
	if req.SigningKey != "" {
		signature, err := s.signPolicyBuild(build, req.SigningKey)
		if err != nil {
			return nil, fmt.Errorf("build signing failed: %w", err)
		}
		build.Signature = signature
	}
	
	// Store build
	s.builds[buildID] = build
	
	// Generate artifacts
	artifacts, err := s.generateBuildArtifacts(build)
	if err != nil {
		return nil, fmt.Errorf("artifact generation failed: %w", err)
	}
	
	return &PolicyBuildResponse{
		BuildID:       buildID,
		DFAHash:       dfaHash,
		AutomataHash:  automataHash,
		LabelerHash:   labelerHash,
		ProofInputs:   map[string]interface{}{"dfa": dfa, "labeler": labeler},
		Artifacts:     artifacts,
		Signature:     build.Signature,
		Status:        "success",
		Timestamp:     time.Now(),
		ExecutionTime: int(time.Since(startTime).Milliseconds()),
	}, nil
}

// compileActionDSLToDFA converts ActionDSL policy to DFA
func (s *BuildOrchestrator) compileActionDSLToDFA(actionDSL map[string]interface{}) (CompiledDFA, error) {
	var states []DFAState
	var transitions []DFATransition
	var acceptStates []int
	var rejectStates []int
	
	// Create initial state
	states = append(states, DFAState{
		StateID: 0,
		Name:    "initial",
		Type:    "initial",
	})
	
	stateCounter := 1
	
	// Process rules from ActionDSL
	if rules, ok := actionDSL["rules"].([]interface{}); ok {
		for _, rule := range rules {
			if ruleMap, ok := rule.(map[string]interface{}); ok {
				newStates, newTransitions := s.compileRule(ruleMap, &stateCounter)
				states = append(states, newStates...)
				transitions = append(transitions, newTransitions...)
			}
		}
	}
	
	// Add accept and reject states
	acceptState := stateCounter
	rejectState := stateCounter + 1
	
	states = append(states, 
		DFAState{StateID: acceptState, Name: "accept", Type: "accept"},
		DFAState{StateID: rejectState, Name: "reject", Type: "reject"},
	)
	
	acceptStates = append(acceptStates, acceptState)
	rejectStates = append(rejectStates, rejectState)
	
	return CompiledDFA{
		States:       states,
		Transitions:  transitions,
		InitialState: 0,
		AcceptStates: acceptStates,
		RejectStates: rejectStates,
		Metadata: map[string]string{
			"compiled_at": time.Now().Format(time.RFC3339),
			"compiler":    "build-orchestrator-v1.0.0",
		},
	}, nil
}

// compileRule converts a single rule to DFA states and transitions
func (s *BuildOrchestrator) compileRule(rule map[string]interface{}, stateCounter *int) ([]DFAState, []DFATransition) {
	var states []DFAState
	var transitions []DFATransition
	
	ruleType, _ := rule["type"].(string)
	ruleID, _ := rule["rule_id"].(string)
	
	// Create state for this rule
	ruleState := *stateCounter
	*stateCounter++
	
	states = append(states, DFAState{
		StateID: ruleState,
		Name:    fmt.Sprintf("rule_%s", ruleID),
		Type:    "intermediate",
		Metadata: map[string]string{
			"rule_type": ruleType,
			"rule_id":   ruleID,
		},
	})
	
	// Create transition from initial state
	trigger := s.generateTriggerFromRule(rule)
	guard := s.generateGuardFromRule(rule)
	
	transitions = append(transitions, DFATransition{
		FromState: 0,
		ToState:   ruleState,
		Trigger:   trigger,
		Guard:     guard,
		Action:    ruleType,
		Metadata: map[string]string{
			"rule_id": ruleID,
		},
	})
	
	return states, transitions
}

// generateTriggerFromRule creates DFA trigger from rule
func (s *BuildOrchestrator) generateTriggerFromRule(rule map[string]interface{}) string {
	if action, ok := rule["action"].(map[string]interface{}); ok {
		if actionType, ok := action["type"].(string); ok {
			if tool, ok := action["tool"].(string); ok {
				return fmt.Sprintf("%s:%s", actionType, tool)
			}
			return actionType
		}
	}
	
	return "any"
}

// generateGuardFromRule creates DFA guard from rule
func (s *BuildOrchestrator) generateGuardFromRule(rule map[string]interface{}) string {
	if guard, ok := rule["guard"].(map[string]interface{}); ok {
		guardData, _ := json.Marshal(guard)
		return string(guardData)
	}
	
	return "true"
}

// generateLabelerConfig creates IFC labeler configuration
func (s *BuildOrchestrator) generateLabelerConfig(actionDSL map[string]interface{}) LabelerConfig {
	var labels []Label
	var labelRules []LabelRule
	var flowPolicies []FlowPolicy
	
	// Default labels
	labels = append(labels, 
		Label{Name: "public", Level: 0, Categories: []string{"unclassified"}},
		Label{Name: "internal", Level: 1, Categories: []string{"internal"}},
		Label{Name: "confidential", Level: 2, Categories: []string{"confidential"}},
		Label{Name: "secret", Level: 3, Categories: []string{"secret"}},
	)
	
	// Generate labeling rules from policy
	if rules, ok := actionDSL["rules"].([]interface{}); ok {
		for _, rule := range rules {
			if ruleMap, ok := rule.(map[string]interface{}); ok {
				labelRule := s.generateLabelRuleFromPolicyRule(ruleMap)
				if labelRule != nil {
					labelRules = append(labelRules, *labelRule)
				}
			}
		}
	}
	
	// Default flow policies (allow upward flow, deny downward)
	for i := 0; i < len(labels); i++ {
		for j := i; j < len(labels); j++ {
			flowPolicies = append(flowPolicies, FlowPolicy{
				From:    labels[i].Name,
				To:      labels[j].Name,
				Allowed: true,
			})
		}
	}
	
	return LabelerConfig{
		Labels:       labels,
		LabelRules:   labelRules,
		FlowPolicies: flowPolicies,
		Metadata: map[string]string{
			"generated_at": time.Now().Format(time.RFC3339),
			"version":      "1.0.0",
		},
	}
}

// generateLabelRuleFromPolicyRule creates labeling rule from policy rule
func (s *BuildOrchestrator) generateLabelRuleFromPolicyRule(rule map[string]interface{}) *LabelRule {
	if action, ok := rule["action"].(map[string]interface{}); ok {
		if actionType, ok := action["type"].(string); ok {
			// Create labeling rule based on action type
			switch actionType {
			case "read":
				return &LabelRule{
					Pattern:   "read:*",
					Label:     "internal",
					Condition: "default_read_label",
				}
			case "write":
				return &LabelRule{
					Pattern:   "write:*",
					Label:     "confidential",
					Condition: "default_write_label",
				}
			case "call":
				if tool, ok := action["tool"].(string); ok {
					return &LabelRule{
						Pattern:   fmt.Sprintf("call:%s", tool),
						Label:     "internal",
						Condition: fmt.Sprintf("tool_%s_label", tool),
					}
				}
			}
		}
	}
	
	return nil
}

// signPolicyBuild creates cryptographic signature for policy build
func (s *BuildOrchestrator) signPolicyBuild(build PolicyBuild, signingKey string) (string, error) {
	// Create canonical representation for signing
	buildData, err := json.Marshal(map[string]interface{}{
		"build_id":      build.BuildID,
		"policy_hash":   build.PolicyHash,
		"proof_hash":    build.ProofHash,
		"dfa_hash":      build.DFAHash,
		"automata_hash": build.AutomataHash,
		"labeler_hash":  build.LabelerHash,
		"created_at":    build.CreatedAt.Unix(),
	})
	if err != nil {
		return "", err
	}
	
	// Calculate signature (simplified - in practice would use proper crypto)
	hash := sha256.Sum256(buildData)
	signature := fmt.Sprintf("sig_%x", hash)
	
	return signature, nil
}

// generateBuildArtifacts creates build artifacts
func (s *BuildOrchestrator) generateBuildArtifacts(build PolicyBuild) ([]string, error) {
	var artifacts []string
	
	// Create build directory
	buildDir := filepath.Join(s.cachePath, build.BuildID)
	if err := os.MkdirAll(buildDir, 0755); err != nil {
		return nil, err
	}
	
	// Write DFA artifact
	dfaPath := filepath.Join(buildDir, "compiled_dfa.json")
	dfaData, err := json.MarshalIndent(build.CompiledDFA, "", "  ")
	if err != nil {
		return nil, err
	}
	if err := os.WriteFile(dfaPath, dfaData, 0644); err != nil {
		return nil, err
	}
	artifacts = append(artifacts, dfaPath)
	
	// Write labeler artifact
	labelerPath := filepath.Join(buildDir, "labeler_config.json")
	labelerData, err := json.MarshalIndent(build.Labeler, "", "  ")
	if err != nil {
		return nil, err
	}
	if err := os.WriteFile(labelerPath, labelerData, 0644); err != nil {
		return nil, err
	}
	artifacts = append(artifacts, labelerPath)
	
	// Write build manifest
	manifestPath := filepath.Join(buildDir, "build_manifest.json")
	manifestData, err := json.MarshalIndent(build, "", "  ")
	if err != nil {
		return nil, err
	}
	if err := os.WriteFile(manifestPath, manifestData, 0644); err != nil {
		return nil, err
	}
	artifacts = append(artifacts, manifestPath)
	
	return artifacts, nil
}

// calculateDFAHash computes hash for DFA
func (s *BuildOrchestrator) calculateDFAHash(dfa CompiledDFA) string {
	data, _ := json.Marshal(dfa)
	hash := sha256.Sum256(data)
	return fmt.Sprintf("%x", hash)
}

// calculateAutomataHash computes hash for automata structure
func (s *BuildOrchestrator) calculateAutomataHash(dfa CompiledDFA) string {
	// Hash only the structural elements (states, transitions)
	structure := map[string]interface{}{
		"states":        dfa.States,
		"transitions":   dfa.Transitions,
		"initial_state": dfa.InitialState,
		"accept_states": dfa.AcceptStates,
		"reject_states": dfa.RejectStates,
	}
	
	data, _ := json.Marshal(structure)
	hash := sha256.Sum256(data)
	return fmt.Sprintf("%x", hash)
}

// calculateLabelerHash computes hash for labeler configuration
func (s *BuildOrchestrator) calculateLabelerHash(labeler LabelerConfig) string {
	data, _ := json.Marshal(labeler)
	hash := sha256.Sum256(data)
	return fmt.Sprintf("%x", hash)
}

// HTTP handlers
func (s *BuildOrchestrator) buildPolicyHandler(c *gin.Context) {
	var req PolicyBuildRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	resp, err := s.BuildPolicy(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, resp)
}

func (s *BuildOrchestrator) getBuildHandler(c *gin.Context) {
	buildID := c.Param("id")
	
	build, exists := s.builds[buildID]
	if !exists {
		c.JSON(http.StatusNotFound, gin.H{"error": "Build not found"})
		return
	}
	
	c.JSON(http.StatusOK, build)
}

func (s *BuildOrchestrator) listBuildsHandler(c *gin.Context) {
	var builds []PolicyBuild
	for _, build := range s.builds {
		builds = append(builds, build)
	}
	
	c.JSON(http.StatusOK, gin.H{
		"builds": builds,
		"count":  len(builds),
	})
}

func (s *BuildOrchestrator) healthHandler(c *gin.Context) {
	c.JSON(http.StatusOK, gin.H{
		"status":    "healthy",
		"service":   "build-orchestrator",
		"version":   "1.0.0",
		"timestamp": time.Now(),
		"builds":    len(s.builds),
	})
}

func main() {
	// Initialize service
	service := NewBuildOrchestrator()
	
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
		v1.POST("/policy/build", service.buildPolicyHandler)
		v1.GET("/builds/:id", service.getBuildHandler)
		v1.GET("/builds", service.listBuildsHandler)
		v1.GET("/health", service.healthHandler)
	}
	
	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8003"
	}
	
	log.Printf("Build Orchestrator starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}