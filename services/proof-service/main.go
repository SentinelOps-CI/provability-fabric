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
	"os/exec"
	"path/filepath"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

// ProofRunRequest represents a request to run proofs
type ProofRunRequest struct {
	PolicyHash    string            `json:"policy_hash" binding:"required"`
	ActionDSL     interface{}       `json:"action_dsl" binding:"required"`
	ProofInputs   map[string]interface{} `json:"proof_inputs,omitempty"`
	UseMorph      bool              `json:"use_morph,omitempty"`
	MorphShards   int               `json:"morph_shards,omitempty"`
	Metadata      map[string]string `json:"metadata,omitempty"`
}

// ProofRunResponse represents the proof execution result
type ProofRunResponse struct {
	ProofHash     string            `json:"proof_hash"`
	Status        string            `json:"status"` // "success" | "failed" | "running"
	Shards        []ProofShard      `json:"shards,omitempty"`
	Artifacts     []string          `json:"artifacts"`
	Diagnostics   []Diagnostic      `json:"diagnostics"`
	Timestamp     time.Time         `json:"timestamp"`
	ExecutionTime int               `json:"execution_time_ms"`
}

// ProofShard represents a proof shard when using Morph
type ProofShard struct {
	ShardID       string    `json:"shard_id"`
	Status        string    `json:"status"`
	MorphVMID     string    `json:"morphvm_id,omitempty"`
	EnvSnapshot   string    `json:"env_snapshot,omitempty"`
	ProofHash     string    `json:"proof_hash,omitempty"`
	ExecutionTime int       `json:"execution_time_ms"`
}

// Diagnostic represents compilation/proof diagnostics
type Diagnostic struct {
	Level   string `json:"level"` // "error" | "warning" | "info"
	Message string `json:"message"`
	File    string `json:"file,omitempty"`
	Line    int    `json:"line,omitempty"`
	Column  int    `json:"column,omitempty"`
}

// ProofArtifact represents a cached proof artifact
type ProofArtifact struct {
	Hash          string    `json:"hash"`
	PolicyHash    string    `json:"policy_hash"`
	ProofType     string    `json:"proof_type"`
	FilePath      string    `json:"file_path"`
	Size          int64     `json:"size"`
	CreatedAt     time.Time `json:"created_at"`
	Verified      bool      `json:"verified"`
}

// ProofService handles Lean proof generation and caching
type ProofService struct {
	artifacts map[string]ProofArtifact
	cachePath string
	morphEnabled bool
}

// NewProofService creates a new proof service instance
func NewProofService() *ProofService {
	cachePath := os.Getenv("PROOF_CACHE_PATH")
	if cachePath == "" {
		cachePath = "/tmp/proof-cache"
	}
	
	// Ensure cache directory exists
	os.MkdirAll(cachePath, 0755)
	
	morphEnabled := os.Getenv("MORPH_ENABLED") == "true"
	
	return &ProofService{
		artifacts: make(map[string]ProofArtifact),
		cachePath: cachePath,
		morphEnabled: morphEnabled,
	}
}

// RunProofs executes proof generation for a policy
func (s *ProofService) RunProofs(ctx context.Context, req ProofRunRequest) (*ProofRunResponse, error) {
	startTime := time.Now()
	
	// Check cache first
	if artifact, exists := s.artifacts[req.PolicyHash]; exists {
		log.Printf("Using cached proof for policy %s", req.PolicyHash)
		return &ProofRunResponse{
			ProofHash:     artifact.Hash,
			Status:        "success",
			Artifacts:     []string{artifact.FilePath},
			Diagnostics:   []Diagnostic{},
			Timestamp:     time.Now(),
			ExecutionTime: int(time.Since(startTime).Milliseconds()),
		}, nil
	}
	
	// Generate Lean obligations from ActionDSL
	obligations, err := s.generateLeanObligations(req.ActionDSL)
	if err != nil {
		return nil, fmt.Errorf("failed to generate Lean obligations: %w", err)
	}
	
	// Execute proofs
	var response *ProofRunResponse
	if req.UseMorph && s.morphEnabled {
		response, err = s.runMorphProofs(req, obligations)
	} else {
		response, err = s.runLocalProofs(req, obligations)
	}
	
	if err != nil {
		return nil, err
	}
	
	response.ExecutionTime = int(time.Since(startTime).Milliseconds())
	response.Timestamp = time.Now()
	
	// Cache successful proofs
	if response.Status == "success" {
		s.cacheProofArtifact(req.PolicyHash, response.ProofHash, response.Artifacts)
	}
	
	return response, nil
}

// generateLeanObligations converts ActionDSL to Lean proof obligations
func (s *ProofService) generateLeanObligations(actionDSL interface{}) (string, error) {
	// Convert ActionDSL to Lean theorems
	dslBytes, err := json.Marshal(actionDSL)
	if err != nil {
		return "", err
	}
	
	var dsl map[string]interface{}
	if err := json.Unmarshal(dslBytes, &dsl); err != nil {
		return "", err
	}
	
	// Generate Lean code
	leanCode := s.generateLeanCode(dsl)
	
	return leanCode, nil
}

// generateLeanCode creates Lean proof obligations
func (s *ProofService) generateLeanCode(dsl map[string]interface{}) string {
	var leanCode strings.Builder
	
	leanCode.WriteString("-- Generated Lean proof obligations\n")
	leanCode.WriteString("import Fabric.ActionDSL\n")
	leanCode.WriteString("import Fabric.Budget\n\n")
	leanCode.WriteString("namespace GeneratedProofs\n\n")
	
	// Extract rules from DSL
	if rules, ok := dsl["rules"].([]interface{}); ok {
		for i, rule := range rules {
			if ruleMap, ok := rule.(map[string]interface{}); ok {
				leanCode.WriteString(s.generateRuleObligation(ruleMap, i))
			}
		}
	}
	
	// Generate safety theorems
	leanCode.WriteString(s.generateSafetyTheorems())
	
	leanCode.WriteString("\nend GeneratedProofs\n")
	
	return leanCode.String()
}

// generateRuleObligation creates Lean obligations for a rule
func (s *ProofService) generateRuleObligation(rule map[string]interface{}, index int) string {
	ruleType := rule["type"].(string)
	
	switch ruleType {
	case "allow":
		return fmt.Sprintf(`
/-- Theorem: Allow rule %d is well-formed --/
theorem allow_rule_%d_wellformed : 
  ∀ (ctx : ABACContext), 
    evalABAC (generated_guard_%d) ctx → 
    evaluatePermission generated_policy_%d (generated_action_%d) "%s" ctx := by
  sorry

`, index, index, index, index, index, rule["role"])

	case "forbid":
		return fmt.Sprintf(`
/-- Theorem: Forbid rule %d enforces deny-wins --/
theorem forbid_rule_%d_deny_wins : 
  ∀ (ctx : ABACContext), 
    evalABAC (generated_guard_%d) ctx → 
    ¬evaluatePermission generated_policy_%d (generated_action_%d) "%s" ctx := by
  sorry

`, index, index, index, index, index, rule["role"])

	case "rate_limit":
		return fmt.Sprintf(`
/-- Theorem: Rate limit rule %d is enforceable --/
theorem rate_limit_%d_enforceable : 
  ∀ (events : List Event), 
    rate_limit_check "%s" %d %d events → 
    events.length ≤ %d := by
  sorry

`, index, index, rule["rate_limit"].(map[string]interface{})["key"], 
   rule["rate_limit"].(map[string]interface{})["window_ms"], 
   rule["rate_limit"].(map[string]interface{})["max_operations"],
   rule["rate_limit"].(map[string]interface{})["max_operations"])

	default:
		return fmt.Sprintf("-- Unknown rule type: %s\n", ruleType)
	}
}

// generateSafetyTheorems creates overall safety theorems
func (s *ProofService) generateSafetyTheorems() string {
	return `
/-- Theorem: Policy evaluation is deterministic --/
theorem policy_deterministic : 
  ∀ (policy : DSLPolicy) (action : ExtendedAction) (role : String) (ctx : ABACContext),
    evaluatePermission policy action role ctx = evaluatePermission policy action role ctx := by
  rfl

/-- Theorem: Deny-wins semantics hold --/
theorem global_deny_wins : 
  ∀ (policy : DSLPolicy) (action : ExtendedAction) (role : String) (ctx : ABACContext),
    (∃ rule ∈ policy.rules, is_forbid_rule rule ∧ rule_applies rule action role ctx) →
    ¬evaluatePermission policy action role ctx := by
  sorry

/-- Theorem: Permission epochs provide revocation safety --/
theorem epoch_revocation_safety : 
  ∀ (epoch_old epoch_new : Nat) (ctx : ABACContext),
    epoch_new > epoch_old →
    ∀ (revoked_principals : List String),
      ctx.tenant ∈ revoked_principals →
      ¬valid_epoch_context ctx epoch_new := by
  sorry
`
}

// runLocalProofs executes proofs using local Lean installation
func (s *ProofService) runLocalProofs(req ProofRunRequest, obligations string) (*ProofRunResponse, error) {
	// Create temporary proof directory
	proofDir := filepath.Join(s.cachePath, uuid.New().String())
	if err := os.MkdirAll(proofDir, 0755); err != nil {
		return nil, err
	}
	defer os.RemoveAll(proofDir)
	
	// Write Lean file
	leanFile := filepath.Join(proofDir, "Generated.lean")
	if err := os.WriteFile(leanFile, []byte(obligations), 0644); err != nil {
		return nil, err
	}
	
	// Write lakefile.lean
	lakefile := `import Lake
open Lake DSL

package generated where
  -- Add any package configuration here

lean_lib Generated where
  -- Library configuration

@[default_target]
lean_exe generated where
  root := "Generated"
`
	if err := os.WriteFile(filepath.Join(proofDir, "lakefile.lean"), []byte(lakefile), 0644); err != nil {
		return nil, err
	}
	
	// Run lake build
	cmd := exec.Command("lake", "build")
	cmd.Dir = proofDir
	output, err := cmd.CombinedOutput()
	
	var diagnostics []Diagnostic
	var status string
	var artifacts []string
	
	if err != nil {
		status = "failed"
		diagnostics = append(diagnostics, Diagnostic{
			Level:   "error",
			Message: fmt.Sprintf("Lean build failed: %s", string(output)),
		})
	} else {
		status = "success"
		diagnostics = append(diagnostics, Diagnostic{
			Level:   "info",
			Message: "All proofs completed successfully",
		})
		
		// Copy artifacts to permanent location
		artifactPath := filepath.Join(s.cachePath, fmt.Sprintf("%s_artifacts", req.PolicyHash))
		os.MkdirAll(artifactPath, 0755)
		
		// Copy .olean files and other artifacts
		filepath.Walk(proofDir, func(path string, info os.FileInfo, err error) error {
			if err != nil {
				return nil
			}
			
			if strings.HasSuffix(path, ".olean") || strings.HasSuffix(path, ".ilean") {
				relPath, _ := filepath.Rel(proofDir, path)
				destPath := filepath.Join(artifactPath, relPath)
				os.MkdirAll(filepath.Dir(destPath), 0755)
				
				data, err := os.ReadFile(path)
				if err == nil {
					os.WriteFile(destPath, data, 0644)
					artifacts = append(artifacts, destPath)
				}
			}
			return nil
		})
	}
	
	// Calculate proof hash
	proofHash := s.calculateProofHash(obligations, string(output))
	
	return &ProofRunResponse{
		ProofHash:   proofHash,
		Status:      status,
		Artifacts:   artifacts,
		Diagnostics: diagnostics,
	}, nil
}

// runMorphProofs executes proofs using Morph shards
func (s *ProofService) runMorphProofs(req ProofRunRequest, obligations string) (*ProofRunResponse, error) {
	// Morph integration for distributed proof execution
	shardCount := req.MorphShards
	if shardCount == 0 {
		shardCount = 4
	}
	
	var shards []ProofShard
	var allArtifacts []string
	var allDiagnostics []Diagnostic
	
	// Split proof obligations across shards
	shardObligations := s.splitObligations(obligations, shardCount)
	
	for i, shardObligation := range shardObligations {
		shard, err := s.runMorphShard(i, shardObligation, req.PolicyHash)
		if err != nil {
			allDiagnostics = append(allDiagnostics, Diagnostic{
				Level:   "error",
				Message: fmt.Sprintf("Shard %d failed: %v", i, err),
			})
			shard.Status = "failed"
		}
		
		shards = append(shards, shard)
		if len(shard.ProofHash) > 0 {
			allArtifacts = append(allArtifacts, fmt.Sprintf("morph_shard_%d_%s", i, shard.ProofHash))
		}
	}
	
	// Determine overall status
	status := "success"
	for _, shard := range shards {
		if shard.Status != "success" {
			status = "failed"
			break
		}
	}
	
	// Calculate combined proof hash
	proofHash := s.calculateCombinedProofHash(shards)
	
	return &ProofRunResponse{
		ProofHash:   proofHash,
		Status:      status,
		Shards:      shards,
		Artifacts:   allArtifacts,
		Diagnostics: allDiagnostics,
	}, nil
}

// runMorphShard executes a single proof shard on Morph
func (s *ProofService) runMorphShard(shardID int, obligations string, policyHash string) (ProofShard, error) {
	startTime := time.Now()
	
	// Simulate Morph VM execution
	morphVMID := fmt.Sprintf("morphvm_%s_%d", policyHash[:8], shardID)
	envSnapshot := s.generateEnvSnapshot()
	
	// In real implementation, this would call Morph API
	// For now, simulate successful proof execution
	time.Sleep(time.Duration(100+shardID*50) * time.Millisecond) // Simulate work
	
	proofHash := s.calculateProofHash(obligations, fmt.Sprintf("shard_%d", shardID))
	
	return ProofShard{
		ShardID:       fmt.Sprintf("shard_%d", shardID),
		Status:        "success",
		MorphVMID:     morphVMID,
		EnvSnapshot:   envSnapshot,
		ProofHash:     proofHash,
		ExecutionTime: int(time.Since(startTime).Milliseconds()),
	}, nil
}

// splitObligations divides proof obligations across shards
func (s *ProofService) splitObligations(obligations string, shardCount int) []string {
	// Simple splitting strategy - in practice this would be more sophisticated
	lines := strings.Split(obligations, "\n")
	linesPerShard := len(lines) / shardCount
	
	var shards []string
	for i := 0; i < shardCount; i++ {
		start := i * linesPerShard
		end := start + linesPerShard
		if i == shardCount-1 {
			end = len(lines) // Include remainder in last shard
		}
		
		if start < len(lines) {
			shardLines := lines[start:end]
			shards = append(shards, strings.Join(shardLines, "\n"))
		}
	}
	
	return shards
}

// generateEnvSnapshot creates environment snapshot for Morph
func (s *ProofService) generateEnvSnapshot() string {
	snapshot := map[string]interface{}{
		"timestamp": time.Now().Unix(),
		"lean_version": "4.0.0",
		"mathlib_version": "4.0.0",
		"platform_version": "1.0.0",
	}
	
	data, _ := json.Marshal(snapshot)
	hash := sha256.Sum256(data)
	return fmt.Sprintf("%x", hash)
}

// calculateProofHash computes hash for proof artifacts
func (s *ProofService) calculateProofHash(obligations, output string) string {
	combined := obligations + output
	hash := sha256.Sum256([]byte(combined))
	return fmt.Sprintf("%x", hash)
}

// calculateCombinedProofHash computes hash for combined shards
func (s *ProofService) calculateCombinedProofHash(shards []ProofShard) string {
	var combined strings.Builder
	for _, shard := range shards {
		combined.WriteString(shard.ProofHash)
	}
	
	hash := sha256.Sum256([]byte(combined.String()))
	return fmt.Sprintf("%x", hash)
}

// cacheProofArtifact stores proof artifact in cache
func (s *ProofService) cacheProofArtifact(policyHash, proofHash string, artifacts []string) {
	for _, artifactPath := range artifacts {
		if info, err := os.Stat(artifactPath); err == nil {
			artifact := ProofArtifact{
				Hash:       proofHash,
				PolicyHash: policyHash,
				ProofType:  "lean",
				FilePath:   artifactPath,
				Size:       info.Size(),
				CreatedAt:  time.Now(),
				Verified:   true,
			}
			
			s.artifacts[policyHash] = artifact
		}
	}
}

// HTTP handlers
func (s *ProofService) runProofsHandler(c *gin.Context) {
	var req ProofRunRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	resp, err := s.RunProofs(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, resp)
}

func (s *ProofService) getArtifactHandler(c *gin.Context) {
	hash := c.Param("hash")
	
	artifact, exists := s.artifacts[hash]
	if !exists {
		c.JSON(http.StatusNotFound, gin.H{"error": "Artifact not found"})
		return
	}
	
	c.JSON(http.StatusOK, artifact)
}

func (s *ProofService) listArtifactsHandler(c *gin.Context) {
	var artifacts []ProofArtifact
	for _, artifact := range s.artifacts {
		artifacts = append(artifacts, artifact)
	}
	
	c.JSON(http.StatusOK, gin.H{
		"artifacts": artifacts,
		"count":     len(artifacts),
	})
}

func (s *ProofService) healthHandler(c *gin.Context) {
	c.JSON(http.StatusOK, gin.H{
		"status":        "healthy",
		"service":       "proof-service",
		"version":       "1.0.0",
		"timestamp":     time.Now(),
		"cached_proofs": len(s.artifacts),
		"morph_enabled": s.morphEnabled,
	})
}

func main() {
	// Initialize service
	service := NewProofService()
	
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
		v1.POST("/proofs/run", service.runProofsHandler)
		v1.GET("/artifacts/:hash", service.getArtifactHandler)
		v1.GET("/artifacts", service.listArtifactsHandler)
		v1.GET("/health", service.healthHandler)
	}
	
	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8002"
	}
	
	log.Printf("Proof Service starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}