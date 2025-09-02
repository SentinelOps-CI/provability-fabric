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
	"os/exec"
	"path/filepath"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

// ReplayRequest represents a request to start a replay
type ReplayRequest struct {
	DecisionID    string            `json:"decision_id" binding:"required"`
	TraceFile     string            `json:"trace_file,omitempty"`
	Config        ReplayConfig      `json:"config,omitempty"`
	UseMorph      bool              `json:"use_morph,omitempty"`
	Metadata      map[string]string `json:"metadata,omitempty"`
}

// ReplayResponse represents the replay initiation response
type ReplayResponse struct {
	JobID     string    `json:"job_id"`
	Status    string    `json:"status"`
	StartedAt time.Time `json:"started_at"`
}

// ReplayStatus represents the status of a replay job
type ReplayStatus struct {
	JobID            string    `json:"job_id"`
	Status           string    `json:"status"` // "running" | "completed" | "failed"
	Progress         float64   `json:"progress"`
	LowViewMatchPct  float64   `json:"low_view_match_pct"`
	Outputs          []string  `json:"outputs"`
	Artifacts        []string  `json:"artifacts"`
	StartedAt        time.Time `json:"started_at"`
	CompletedAt      *time.Time `json:"completed_at,omitempty"`
	ExecutionTimeMs  int       `json:"execution_time_ms"`
	DriftDetected    bool      `json:"drift_detected"`
	ErrorMessage     string    `json:"error_message,omitempty"`
}

// ReplayConfig represents replay configuration
type ReplayConfig struct {
	Seed              int     `json:"seed"`
	Locale            string  `json:"locale"`
	Timezone          string  `json:"timezone"`
	ChunkSize         int     `json:"chunk_size"`
	FlushCadenceMs    int     `json:"flush_cadence_ms"`
	PaddingPolicy     string  `json:"padding_policy"`
	DriftThreshold    float64 `json:"drift_threshold"`
}

// ReplayJob represents an active replay job
type ReplayJob struct {
	JobID       string       `json:"job_id"`
	DecisionID  string       `json:"decision_id"`
	Config      ReplayConfig `json:"config"`
	Status      ReplayStatus `json:"status"`
	TraceFile   string       `json:"trace_file"`
	WorkingDir  string       `json:"working_dir"`
	UseMorph    bool         `json:"use_morph"`
}

// ReplayService handles deterministic replay execution
type ReplayService struct {
	jobs        map[string]*ReplayJob
	workingDir  string
	replayKit   string
}

// NewReplayService creates a new replay service instance
func NewReplayService() *ReplayService {
	workingDir := os.Getenv("REPLAY_WORKING_DIR")
	if workingDir == "" {
		workingDir = "/tmp/replay-jobs"
	}
	os.MkdirAll(workingDir, 0755)
	
	replayKit := os.Getenv("REPLAY_KIT_PATH")
	if replayKit == "" {
		replayKit = "external/TRACE-REPLAY-KIT/runner.py"
	}
	
	return &ReplayService{
		jobs:       make(map[string]*ReplayJob),
		workingDir: workingDir,
		replayKit:  replayKit,
	}
}

// StartReplay initiates a new replay job
func (s *ReplayService) StartReplay(ctx context.Context, req ReplayRequest) (*ReplayResponse, error) {
	jobID := uuid.New().String()
	
	// Set default config
	config := req.Config
	if config.Seed == 0 {
		config.Seed = 42
	}
	if config.Locale == "" {
		config.Locale = "C"
	}
	if config.Timezone == "" {
		config.Timezone = "UTC"
	}
	if config.ChunkSize == 0 {
		config.ChunkSize = 4096
	}
	if config.FlushCadenceMs == 0 {
		config.FlushCadenceMs = 100
	}
	if config.PaddingPolicy == "" {
		config.PaddingPolicy = "fixed"
	}
	if config.DriftThreshold == 0 {
		config.DriftThreshold = 0.001
	}
	
	// Create job working directory
	jobWorkingDir := filepath.Join(s.workingDir, jobID)
	if err := os.MkdirAll(jobWorkingDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create job directory: %w", err)
	}
	
	// Determine trace file
	traceFile := req.TraceFile
	if traceFile == "" {
		// Generate trace file from decision ID
		var err error
		traceFile, err = s.generateTraceFromDecision(req.DecisionID, jobWorkingDir)
		if err != nil {
			return nil, fmt.Errorf("failed to generate trace: %w", err)
		}
	}
	
	// Create job
	job := &ReplayJob{
		JobID:      jobID,
		DecisionID: req.DecisionID,
		Config:     config,
		Status: ReplayStatus{
			JobID:     jobID,
			Status:    "running",
			Progress:  0.0,
			StartedAt: time.Now(),
		},
		TraceFile:  traceFile,
		WorkingDir: jobWorkingDir,
		UseMorph:   req.UseMorph,
	}
	
	// Store job
	s.jobs[jobID] = job
	
	// Start replay execution asynchronously
	go s.executeReplay(job)
	
	return &ReplayResponse{
		JobID:     jobID,
		Status:    "running",
		StartedAt: time.Now(),
	}, nil
}

// GetReplayStatus returns the status of a replay job
func (s *ReplayService) GetReplayStatus(ctx context.Context, jobID string) (*ReplayStatus, error) {
	job, exists := s.jobs[jobID]
	if !exists {
		return nil, fmt.Errorf("job not found: %s", jobID)
	}
	
	return &job.Status, nil
}

// executeReplay runs the actual replay execution
func (s *ReplayService) executeReplay(job *ReplayJob) {
	defer func() {
		if r := recover(); r != nil {
			job.Status.Status = "failed"
			job.Status.ErrorMessage = fmt.Sprintf("Replay panicked: %v", r)
			completedAt := time.Now()
			job.Status.CompletedAt = &completedAt
		}
	}()
	
	log.Printf("Starting replay execution for job %s", job.JobID)
	
	// Update progress
	job.Status.Progress = 0.1
	
	// Write config file
	configFile := filepath.Join(job.WorkingDir, "config.json")
	configData, _ := json.MarshalIndent(job.Config, "", "  ")
	if err := os.WriteFile(configFile, configData, 0644); err != nil {
		job.Status.Status = "failed"
		job.Status.ErrorMessage = fmt.Sprintf("Failed to write config: %v", err)
		return
	}
	
	job.Status.Progress = 0.2
	
	// Execute replay
	if job.UseMorph {
		s.executeMorphReplay(job)
	} else {
		s.executeLocalReplay(job)
	}
}

// executeLocalReplay runs replay using local TRACE-REPLAY-KIT
func (s *ReplayService) executeLocalReplay(job *ReplayJob) {
	configFile := filepath.Join(job.WorkingDir, "config.json")
	
	// Run TRACE-REPLAY-KIT
	cmd := exec.Command("python3", s.replayKit, job.TraceFile, configFile)
	cmd.Dir = job.WorkingDir
	
	output, err := cmd.CombinedOutput()
	
	job.Status.Progress = 0.8
	
	if err != nil {
		job.Status.Status = "failed"
		job.Status.ErrorMessage = fmt.Sprintf("Replay execution failed: %v\nOutput: %s", err, string(output))
		completedAt := time.Now()
		job.Status.CompletedAt = &completedAt
		return
	}
	
	// Parse output
	var result map[string]interface{}
	if err := json.Unmarshal(output, &result); err != nil {
		job.Status.Status = "failed"
		job.Status.ErrorMessage = fmt.Sprintf("Failed to parse replay output: %v", err)
		completedAt := time.Now()
		job.Status.CompletedAt = &completedAt
		return
	}
	
	// Extract results
	if lowViewMatch, ok := result["low_view_match_pct"].(float64); ok {
		job.Status.LowViewMatchPct = lowViewMatch
		job.Status.DriftDetected = lowViewMatch < job.Config.DriftThreshold
	}
	
	if artifacts, ok := result["artifacts"].([]interface{}); ok {
		for _, artifact := range artifacts {
			if artifactStr, ok := artifact.(string); ok {
				job.Status.Artifacts = append(job.Status.Artifacts, artifactStr)
			}
		}
	}
	
	job.Status.Progress = 1.0
	job.Status.Status = "completed"
	completedAt := time.Now()
	job.Status.CompletedAt = &completedAt
	job.Status.ExecutionTimeMs = int(completedAt.Sub(job.Status.StartedAt).Milliseconds())
	
	log.Printf("Replay job %s completed: low_view_match=%.3f", job.JobID, job.Status.LowViewMatchPct)
}

// executeMorphReplay runs replay using Morph distributed execution
func (s *ReplayService) executeMorphReplay(job *ReplayJob) {
	// Simulate Morph replay execution
	log.Printf("Starting Morph replay for job %s", job.JobID)
	
	// Simulate distributed execution
	time.Sleep(2 * time.Second)
	job.Status.Progress = 0.5
	
	time.Sleep(2 * time.Second)
	job.Status.Progress = 0.9
	
	// Simulate successful completion
	job.Status.LowViewMatchPct = 0.9995 // High match rate
	job.Status.DriftDetected = false
	job.Status.Progress = 1.0
	job.Status.Status = "completed"
	completedAt := time.Now()
	job.Status.CompletedAt = &completedAt
	job.Status.ExecutionTimeMs = int(completedAt.Sub(job.Status.StartedAt).Milliseconds())
	
	// Generate mock artifacts
	job.Status.Artifacts = []string{
		filepath.Join(job.WorkingDir, "morph_lowview_report.json"),
		filepath.Join(job.WorkingDir, "morph_execution.log"),
	}
	
	log.Printf("Morph replay job %s completed", job.JobID)
}

// generateTraceFromDecision creates a trace file from a decision ID
func (s *ReplayService) generateTraceFromDecision(decisionID, workingDir string) (string, error) {
	// In production, this would query the Evidence Service for the decision
	// and reconstruct the trace from CERT-V1 certificates
	
	traceFile := filepath.Join(workingDir, "trace.json")
	
	// Generate mock trace
	trace := map[string]interface{}{
		"session_id": decisionID,
		"events": []map[string]interface{}{
			{
				"type":       "permission_check",
				"timestamp":  time.Now().Unix(),
				"action":     "call",
				"principal":  "user_001",
				"tool_name":  "fraud_scorer",
				"args":       []string{"transaction_123"},
			},
			{
				"type":       "tool_call",
				"timestamp":  time.Now().Unix() + 1,
				"tool_name":  "fraud_scorer",
				"args":       []string{"transaction_123"},
				"result":     map[string]interface{}{"score": 0.85},
			},
			{
				"type":       "egress",
				"timestamp":  time.Now().Unix() + 2,
				"data":       "fraud_score_result",
				"chunk_size": 4096,
			},
		},
		"environment": map[string]interface{}{
			"seed":              42,
			"locale":           "C",
			"timezone":         "UTC",
			"sidecar_version":  "1.0.0",
		},
		"metadata": map[string]interface{}{
			"decision_id":    decisionID,
			"generated_at":   time.Now().Unix(),
			"trace_version":  "1.0.0",
		},
		"expected_outputs": []string{
			"permission_check:call:decision_abc123",
			"tool_call:fraud_scorer:result_def456",
			"egress:chunk_789abc",
		},
	}
	
	traceData, err := json.MarshalIndent(trace, "", "  ")
	if err != nil {
		return "", err
	}
	
	if err := os.WriteFile(traceFile, traceData, 0644); err != nil {
		return "", err
	}
	
	return traceFile, nil
}

// HTTP handlers
func (s *ReplayService) startReplayHandler(c *gin.Context) {
	var req ReplayRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	resp, err := s.StartReplay(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, resp)
}

func (s *ReplayService) getReplayStatusHandler(c *gin.Context) {
	jobID := c.Param("jobId")
	
	status, err := s.GetReplayStatus(c.Request.Context(), jobID)
	if err != nil {
		c.JSON(http.StatusNotFound, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, status)
}

func (s *ReplayService) listReplaysHandler(c *gin.Context) {
	var jobs []ReplayStatus
	for _, job := range s.jobs {
		jobs = append(jobs, job.Status)
	}
	
	c.JSON(http.StatusOK, gin.H{
		"jobs":  jobs,
		"count": len(jobs),
	})
}

func (s *ReplayService) downloadArtifactHandler(c *gin.Context) {
	jobID := c.Param("jobId")
	artifactName := c.Param("artifact")
	
	job, exists := s.jobs[jobID]
	if !exists {
		c.JSON(http.StatusNotFound, gin.H{"error": "Job not found"})
		return
	}
	
	// Find artifact file
	artifactPath := filepath.Join(job.WorkingDir, artifactName)
	if _, err := os.Stat(artifactPath); os.IsNotExist(err) {
		c.JSON(http.StatusNotFound, gin.H{"error": "Artifact not found"})
		return
	}
	
	c.Header("Content-Type", "application/octet-stream")
	c.Header("Content-Disposition", fmt.Sprintf("attachment; filename=%s", artifactName))
	c.File(artifactPath)
}

func (s *ReplayService) healthHandler(c *gin.Context) {
	// Check if TRACE-REPLAY-KIT is available
	replayKitStatus := "available"
	if _, err := os.Stat(s.replayKit); os.IsNotExist(err) {
		replayKitStatus = "missing"
	}
	
	c.JSON(http.StatusOK, gin.H{
		"status":           "healthy",
		"service":          "replay-service",
		"version":          "1.0.0",
		"timestamp":        time.Now(),
		"active_jobs":      len(s.jobs),
		"replay_kit":       replayKitStatus,
		"working_dir":      s.workingDir,
	})
}

func main() {
	// Initialize service
	service := NewReplayService()
	
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
		v1.POST("/replay", service.startReplayHandler)
		v1.GET("/replay/:jobId", service.getReplayStatusHandler)
		v1.GET("/replays", service.listReplaysHandler)
		v1.GET("/replay/:jobId/artifact/:artifact", service.downloadArtifactHandler)
		v1.GET("/health", service.healthHandler)
	}
	
	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8005"
	}
	
	log.Printf("Replay Service starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}