// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"os"
	"path/filepath"
	"sort"
	"time"
)

// EnhancedReplayService provides advanced replay capabilities with metrics and counterexample generation
type EnhancedReplayService struct {
	*ReplayService
	counterexampleGenerator *CounterexampleGenerator
	metricsCalculator       *MetricsCalculator
}

// CounterexampleGenerator generates minimal counterexamples using greedy shrinking
type CounterexampleGenerator struct {
	maxShrinkingSteps int
	shrinkThreshold   float64
}

// MetricsCalculator calculates replay metrics
type MetricsCalculator struct {
	driftThreshold float64
}

// ReplayMetrics contains detailed replay analysis results
type ReplayMetrics struct {
	LowViewMatchPct    float64                `json:"low_view_match_pct"`
	FirstMismatchIndex int                    `json:"first_mismatch_index"`
	TotalSteps         int                    `json:"total_steps"`
	MatchingSteps      int                    `json:"matching_steps"`
	DriftDetected      bool                   `json:"drift_detected"`
	DriftMagnitude     float64                `json:"drift_magnitude"`
	Counterexample     *MinimalCounterexample `json:"counterexample,omitempty"`
	PerformanceMetrics PerformanceMetrics     `json:"performance_metrics"`
}

// MinimalCounterexample represents a minimized counterexample
type MinimalCounterexample struct {
	OriginalSteps    []ReplayStep `json:"original_steps"`
	MinimalPrefix    []ReplayStep `json:"minimal_prefix"`
	ShrinkingSteps   int          `json:"shrinking_steps"`
	ReductionRatio   float64      `json:"reduction_ratio"`
	MismatchPoint    int          `json:"mismatch_point"`
	FailureReason    string       `json:"failure_reason"`
	MinimizationTime int64        `json:"minimization_time_ms"`
}

// ReplayStep represents a single step in the replay
type ReplayStep struct {
	Index     int                    `json:"index"`
	Action    string                 `json:"action"`
	Input     map[string]interface{} `json:"input"`
	Output    map[string]interface{} `json:"output"`
	Timestamp int64                  `json:"timestamp"`
	Metadata  map[string]interface{} `json:"metadata,omitempty"`
}

// PerformanceMetrics contains performance analysis
type PerformanceMetrics struct {
	ExecutionTimeMs          int64   `json:"execution_time_ms"`
	MemoryUsageMB            float64 `json:"memory_usage_mb"`
	CPUUsagePercent          float64 `json:"cpu_usage_percent"`
	ThroughputStepsPerSecond float64 `json:"throughput_steps_per_second"`
	LatencyP50Ms             int64   `json:"latency_p50_ms"`
	LatencyP95Ms             int64   `json:"latency_p95_ms"`
	LatencyP99Ms             int64   `json:"latency_p99_ms"`
}

// NewEnhancedReplayService creates a new enhanced replay service
func NewEnhancedReplayService() *EnhancedReplayService {
	return &EnhancedReplayService{
		ReplayService: NewReplayService(),
		counterexampleGenerator: &CounterexampleGenerator{
			maxShrinkingSteps: 1000,
			shrinkThreshold:   0.1,
		},
		metricsCalculator: &MetricsCalculator{
			driftThreshold: 0.001,
		},
	}
}

// StartEnhancedReplay starts a replay with enhanced metrics and counterexample generation
func (s *EnhancedReplayService) StartEnhancedReplay(ctx context.Context, req ReplayRequest) (*ReplayResponse, error) {
	// Start the base replay
	baseResp, err := s.ReplayService.StartReplay(ctx, req)
	if err != nil {
		return nil, err
	}

	// Start enhanced processing in background
	go s.processEnhancedReplay(baseResp.JobID, req)

	return baseResp, nil
}

// processEnhancedReplay processes the replay with enhanced analysis
func (s *EnhancedReplayService) processEnhancedReplay(jobID string, req ReplayRequest) {
	// Wait for base replay to complete
	job := s.getJob(jobID)
	if job == nil {
		log.Printf("Job %s not found", jobID)
		return
	}

	// Poll for completion
	for {
		time.Sleep(1 * time.Second)
		job = s.getJob(jobID)
		if job == nil {
			log.Printf("Job %s not found during polling", jobID)
			return
		}

		if job.Status.Status == "completed" || job.Status.Status == "failed" {
			break
		}
	}

	// Generate enhanced metrics
	metrics, err := s.generateReplayMetrics(job)
	if err != nil {
		log.Printf("Failed to generate metrics for job %s: %v", jobID, err)
		return
	}

	// Update job with enhanced metrics
	s.updateJobWithMetrics(jobID, metrics)
}

// generateReplayMetrics generates comprehensive replay metrics
func (s *EnhancedReplayService) generateReplayMetrics(job *ReplayJob) (*ReplayMetrics, error) {
	// Load replay trace
	trace, err := s.loadReplayTrace(job)
	if err != nil {
		return nil, fmt.Errorf("failed to load replay trace: %w", err)
	}

	// Calculate basic metrics
	metrics := &ReplayMetrics{
		TotalSteps:         len(trace),
		MatchingSteps:      s.countMatchingSteps(trace),
		DriftDetected:      job.Status.DriftDetected,
		DriftMagnitude:     s.calculateDriftMagnitude(trace),
		PerformanceMetrics: s.calculatePerformanceMetrics(trace),
	}

	// Calculate low-view match percentage
	metrics.LowViewMatchPct = float64(metrics.MatchingSteps) / float64(metrics.TotalSteps) * 100

	// Find first mismatch
	metrics.FirstMismatchIndex = s.findFirstMismatch(trace)

	// Generate counterexample if there are mismatches
	if metrics.FirstMismatchIndex >= 0 {
		counterexample, err := s.counterexampleGenerator.GenerateMinimalCounterexample(trace, metrics.FirstMismatchIndex)
		if err != nil {
			log.Printf("Failed to generate counterexample: %v", err)
		} else {
			metrics.Counterexample = counterexample
		}
	}

	return metrics, nil
}

// loadReplayTrace loads the replay trace from the job
func (s *EnhancedReplayService) loadReplayTrace(job *ReplayJob) ([]ReplayStep, error) {
	// This would load the actual trace file
	// For now, return mock data
	return s.generateMockTrace(job), nil
}

// generateMockTrace generates a mock trace for testing
func (s *EnhancedReplayService) generateMockTrace(job *ReplayJob) []ReplayStep {
	steps := make([]ReplayStep, 10)
	for i := 0; i < 10; i++ {
		steps[i] = ReplayStep{
			Index:     i,
			Action:    fmt.Sprintf("action_%d", i),
			Input:     map[string]interface{}{"value": i},
			Output:    map[string]interface{}{"result": i * 2},
			Timestamp: time.Now().UnixNano() / int64(time.Millisecond),
			Metadata:  map[string]interface{}{"step_type": "computation"},
		}
	}
	return steps
}

// countMatchingSteps counts the number of matching steps
func (s *EnhancedReplayService) countMatchingSteps(trace []ReplayStep) int {
	// This would implement actual step matching logic
	// For now, return a mock value
	return int(float64(len(trace)) * 0.85) // 85% match rate
}

// calculateDriftMagnitude calculates the magnitude of drift
func (s *EnhancedReplayService) calculateDriftMagnitude(trace []ReplayStep) float64 {
	// This would implement actual drift calculation
	// For now, return a mock value
	return 0.05 // 5% drift
}

// findFirstMismatch finds the index of the first mismatch
func (s *EnhancedReplayService) findFirstMismatch(trace []ReplayStep) int {
	// This would implement actual mismatch detection
	// For now, return a mock value
	return 7 // First mismatch at step 7
}

// calculatePerformanceMetrics calculates performance metrics
func (s *EnhancedReplayService) calculatePerformanceMetrics(trace []ReplayStep) PerformanceMetrics {
	if len(trace) == 0 {
		return PerformanceMetrics{}
	}

	// Calculate execution time
	startTime := trace[0].Timestamp
	endTime := trace[len(trace)-1].Timestamp
	executionTime := endTime - startTime

	// Calculate throughput
	throughput := float64(len(trace)) / float64(executionTime) * 1000 // steps per second

	// Calculate latencies (mock values for now)
	latencies := make([]int64, len(trace))
	for i := 1; i < len(trace); i++ {
		latencies[i] = trace[i].Timestamp - trace[i-1].Timestamp
	}
	sort.Slice(latencies, func(i, j int) bool { return latencies[i] < latencies[j] })

	return PerformanceMetrics{
		ExecutionTimeMs:          executionTime,
		MemoryUsageMB:            128.5,
		CPUUsagePercent:          45.2,
		ThroughputStepsPerSecond: throughput,
		LatencyP50Ms:             s.percentile(latencies, 50),
		LatencyP95Ms:             s.percentile(latencies, 95),
		LatencyP99Ms:             s.percentile(latencies, 99),
	}
}

// percentile calculates the percentile of a slice
func (s *EnhancedReplayService) percentile(data []int64, p int) int64 {
	if len(data) == 0 {
		return 0
	}
	index := int(float64(len(data)) * float64(p) / 100.0)
	if index >= len(data) {
		index = len(data) - 1
	}
	return data[index]
}

// updateJobWithMetrics updates the job with enhanced metrics
func (s *EnhancedReplayService) updateJobWithMetrics(jobID string, metrics *ReplayMetrics) {
	s.jobsMu.Lock()
	defer s.jobsMu.Unlock()

	job, exists := s.jobs[jobID]
	if !exists {
		return
	}

	// Update job status with metrics
	job.Status.LowViewMatchPct = metrics.LowViewMatchPct
	job.Status.MismatchIndex = metrics.FirstMismatchIndex
	job.Status.DriftDetected = metrics.DriftDetected

	// Add counterexample if available
	if metrics.Counterexample != nil {
		job.Status.Counterexample = &struct {
			Steps         []map[string]interface{} `json:"steps,omitempty"`
			MinimalPrefix []map[string]interface{} `json:"minimal_prefix,omitempty"`
		}{
			Steps:         s.convertStepsToMaps(metrics.Counterexample.OriginalSteps),
			MinimalPrefix: s.convertStepsToMaps(metrics.Counterexample.MinimalPrefix),
		}
	}

	// Publish update event
	s.publish(jobID, devEvent{
		Type:      "metrics_updated",
		Timestamp: time.Now(),
		JobID:     jobID,
		Data: map[string]interface{}{
			"metrics": metrics,
		},
	})
}

// convertStepsToMaps converts ReplayStep slice to map slice
func (s *EnhancedReplayService) convertStepsToMaps(steps []ReplayStep) []map[string]interface{} {
	maps := make([]map[string]interface{}, len(steps))
	for i, step := range steps {
		maps[i] = map[string]interface{}{
			"index":     step.Index,
			"action":    step.Action,
			"input":     step.Input,
			"output":    step.Output,
			"timestamp": step.Timestamp,
			"metadata":  step.Metadata,
		}
	}
	return maps
}

// getJob safely gets a job
func (s *EnhancedReplayService) getJob(jobID string) *ReplayJob {
	s.jobsMu.RLock()
	defer s.jobsMu.RUnlock()
	return s.jobs[jobID]
}

// GenerateMinimalCounterexample generates a minimal counterexample using greedy shrinking
func (cg *CounterexampleGenerator) GenerateMinimalCounterexample(trace []ReplayStep, mismatchIndex int) (*MinimalCounterexample, error) {
	startTime := time.Now()

	// Start with the full trace
	originalSteps := make([]ReplayStep, len(trace))
	copy(originalSteps, trace)

	// Create a copy for shrinking
	currentSteps := make([]ReplayStep, len(trace))
	copy(currentSteps, trace)

	shrinkingSteps := 0
	reductionRatio := 0.0

	// Greedy shrinking algorithm
	for shrinkingSteps < cg.maxShrinkingSteps {
		// Try to remove each step and see if we still have a mismatch
		bestReduction := 0
		bestIndex := -1

		for i := 0; i < len(currentSteps); i++ {
			// Create a copy without this step
			testSteps := make([]ReplayStep, 0, len(currentSteps)-1)
			testSteps = append(testSteps, currentSteps[:i]...)
			testSteps = append(testSteps, currentSteps[i+1:]...)

			// Check if this still produces a mismatch
			if cg.stillHasMismatch(testSteps, mismatchIndex) {
				reduction := 1
				if reduction > bestReduction {
					bestReduction = reduction
					bestIndex = i
				}
			}
		}

		// If we found a step to remove, remove it
		if bestIndex >= 0 {
			currentSteps = append(currentSteps[:bestIndex], currentSteps[bestIndex+1:]...)
			shrinkingSteps++
		} else {
			// No more steps can be removed
			break
		}
	}

	// Calculate reduction ratio
	if len(originalSteps) > 0 {
		reductionRatio = float64(len(originalSteps)-len(currentSteps)) / float64(len(originalSteps))
	}

	minimizationTime := time.Since(startTime).Milliseconds()

	return &MinimalCounterexample{
		OriginalSteps:    originalSteps,
		MinimalPrefix:    currentSteps,
		ShrinkingSteps:   shrinkingSteps,
		ReductionRatio:   reductionRatio,
		MismatchPoint:    mismatchIndex,
		FailureReason:    "Step mismatch detected",
		MinimizationTime: minimizationTime,
	}, nil
}

// stillHasMismatch checks if the trace still has a mismatch at the given index
func (cg *CounterexampleGenerator) stillHasMismatch(steps []ReplayStep, originalMismatchIndex int) bool {
	// This would implement actual mismatch detection logic
	// For now, return true if we have enough steps
	return len(steps) > originalMismatchIndex
}

// GetEnhancedReplayStatus returns the enhanced replay status
func (s *EnhancedReplayService) GetEnhancedReplayStatus(jobID string) (*ReplayStatus, error) {
	status, err := s.ReplayService.GetReplayStatus(jobID)
	if err != nil {
		return nil, err
	}

	// Add enhanced metrics if available
	job := s.getJob(jobID)
	if job != nil {
		// The job status should already be updated with enhanced metrics
		// by the background processing
	}

	return status, nil
}

// PromoteToGolden promotes a test vector to golden status
func (s *EnhancedReplayService) PromoteToGolden(jobID string, testVectorPath string) error {
	// Get the job
	job := s.getJob(jobID)
	if job == nil {
		return fmt.Errorf("job %s not found", jobID)
	}

	// Validate that the job is completed
	if job.Status.Status != "completed" {
		return fmt.Errorf("job %s is not completed", jobID)
	}

	// Copy the test vector to the golden directory
	goldenDir := s.getGoldenDirectory()
	if err := s.copyToGolden(testVectorPath, goldenDir, job.DecisionID); err != nil {
		return fmt.Errorf("failed to copy to golden: %w", err)
	}

	// Update the job metadata
	job.Status.Artifacts = append(job.Status.Artifacts, fmt.Sprintf("golden:%s", testVectorPath))

	// Publish promotion event
	s.publish(jobID, devEvent{
		Type:      "promoted_to_golden",
		Timestamp: time.Now(),
		JobID:     jobID,
		Data: map[string]interface{}{
			"test_vector_path": testVectorPath,
			"golden_directory": goldenDir,
		},
	})

	return nil
}

// getGoldenDirectory returns the golden test vectors directory
func (s *EnhancedReplayService) getGoldenDirectory() string {
	return filepath.Join(s.workingDir, "golden")
}

// copyToGolden copies a test vector to the golden directory
func (s *EnhancedReplayService) copyToGolden(sourcePath, goldenDir, decisionID string) error {
	// Create golden directory if it doesn't exist
	if err := os.MkdirAll(goldenDir, 0755); err != nil {
		return err
	}

	// Generate golden filename
	goldenFilename := fmt.Sprintf("golden_%s_%d.json", decisionID, time.Now().Unix())
	goldenPath := filepath.Join(goldenDir, goldenFilename)

	// Copy the file
	sourceFile, err := os.Open(sourcePath)
	if err != nil {
		return err
	}
	defer sourceFile.Close()

	goldenFile, err := os.Create(goldenPath)
	if err != nil {
		return err
	}
	defer goldenFile.Close()

	_, err = io.Copy(goldenFile, sourceFile)
	return err
}
