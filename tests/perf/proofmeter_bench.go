// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"net/http"
	"os"
	"sort"
	"sync"
	"time"
)

// BenchmarkConfig holds the benchmark configuration
type BenchmarkConfig struct {
	TargetRPS   int           `json:"target_rps"`
	Duration    time.Duration `json:"duration"`
	Concurrency int           `json:"concurrency"`
	Endpoint    string        `json:"endpoint"`
	Timeout     time.Duration `json:"timeout"`
	OutputFile  string        `json:"output_file"`
	Seed        int64         `json:"seed"`
}

// LatencyResult represents a single latency measurement
type LatencyResult struct {
	Timestamp time.Time     `json:"timestamp"`
	Latency   time.Duration `json:"latency"`
	Success   bool          `json:"success"`
	Error     string        `json:"error,omitempty"`
}

// BenchmarkResult holds the complete benchmark results
type BenchmarkResult struct {
	Config    BenchmarkConfig `json:"config"`
	Results   []LatencyResult `json:"results"`
	Summary   SummaryStats    `json:"summary"`
	Timestamp time.Time       `json:"timestamp"`
}

// SummaryStats holds statistical summary of the benchmark
type SummaryStats struct {
	TotalRequests      int           `json:"total_requests"`
	SuccessfulRequests int           `json:"successful_requests"`
	FailedRequests     int           `json:"failed_requests"`
	SuccessRate        float64       `json:"success_rate"`
	P50Latency         time.Duration `json:"p50_latency"`
	P95Latency         time.Duration `json:"p95_latency"`
	P99Latency         time.Duration `json:"p99_latency"`
	MinLatency         time.Duration `json:"min_latency"`
	MaxLatency         time.Duration `json:"max_latency"`
	AvgLatency         time.Duration `json:"avg_latency"`
	RPS                float64       `json:"actual_rps"`
}

// Worker represents a benchmark worker
type Worker struct {
	id      int
	config  BenchmarkConfig
	client  *http.Client
	results chan LatencyResult
	wg      *sync.WaitGroup
}

// NewWorker creates a new benchmark worker
func NewWorker(id int, config BenchmarkConfig, results chan LatencyResult, wg *sync.WaitGroup) *Worker {
	client := &http.Client{
		Timeout: config.Timeout,
		Transport: &http.Transport{
			MaxIdleConns:        100,
			MaxIdleConnsPerHost: 100,
			IdleConnTimeout:     90 * time.Second,
		},
	}

	return &Worker{
		id:      id,
		config:  config,
		client:  client,
		results: results,
		wg:      wg,
	}
}

// Run executes the benchmark worker
func (w *Worker) Run(ctx context.Context) {
	defer w.wg.Done()

	// Calculate request interval based on target RPS and concurrency
	requestsPerWorker := w.config.TargetRPS / w.config.Concurrency
	interval := time.Second / time.Duration(requestsPerWorker)

	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			w.makeRequest()
		}
	}
}

// makeRequest makes a single HTTP request and records the result
func (w *Worker) makeRequest() {
	start := time.Now()

	// Create a test request payload
	payload := map[string]interface{}{
		"action":   "SendEmail",
		"score":    rand.Intn(100),
		"trace_id": fmt.Sprintf("bench_%d_%d", w.id, start.UnixNano()),
	}

	// Convert payload to JSON
	jsonData, err := json.Marshal(payload)
	if err != nil {
		w.results <- LatencyResult{
			Timestamp: start,
			Latency:   time.Since(start),
			Success:   false,
			Error:     fmt.Sprintf("JSON marshal error: %v", err),
		}
		return
	}

	// Create HTTP request
	req, err := http.NewRequest("POST", w.config.Endpoint, nil)
	if err != nil {
		w.results <- LatencyResult{
			Timestamp: start,
			Latency:   time.Since(start),
			Success:   false,
			Error:     fmt.Sprintf("Request creation error: %v", err),
		}
		return
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("User-Agent", "proofmeter-bench/1.0")

	// Make the request
	resp, err := w.client.Do(req)
	latency := time.Since(start)

	if err != nil {
		w.results <- LatencyResult{
			Timestamp: start,
			Latency:   latency,
			Success:   false,
			Error:     fmt.Sprintf("Request error: %v", err),
		}
		return
	}
	defer resp.Body.Close()

	// Check if request was successful
	success := resp.StatusCode >= 200 && resp.StatusCode < 300

	w.results <- LatencyResult{
		Timestamp: start,
		Latency:   latency,
		Success:   success,
		Error: func() string {
			if !success {
				return fmt.Sprintf("HTTP %d", resp.StatusCode)
			}
			return ""
		}(),
	}
}

// calculatePercentile calculates the nth percentile of latencies
func calculatePercentile(latencies []time.Duration, percentile float64) time.Duration {
	if len(latencies) == 0 {
		return 0
	}

	sort.Slice(latencies, func(i, j int) bool {
		return latencies[i] < latencies[j]
	})

	index := int(float64(len(latencies)-1) * percentile / 100.0)
	return latencies[index]
}

// calculateSummary calculates statistical summary from results
func calculateSummary(results []LatencyResult, duration time.Duration) SummaryStats {
	if len(results) == 0 {
		return SummaryStats{}
	}

	var latencies []time.Duration
	successful := 0
	failed := 0
	totalLatency := time.Duration(0)

	for _, result := range results {
		latencies = append(latencies, result.Latency)
		totalLatency += result.Latency

		if result.Success {
			successful++
		} else {
			failed++
		}
	}

	sort.Slice(latencies, func(i, j int) bool {
		return latencies[i] < latencies[j]
	})

	successRate := float64(successful) / float64(len(results)) * 100
	actualRPS := float64(len(results)) / duration.Seconds()

	return SummaryStats{
		TotalRequests:      len(results),
		SuccessfulRequests: successful,
		FailedRequests:     failed,
		SuccessRate:        successRate,
		P50Latency:         calculatePercentile(latencies, 50),
		P95Latency:         calculatePercentile(latencies, 95),
		P99Latency:         calculatePercentile(latencies, 99),
		MinLatency:         latencies[0],
		MaxLatency:         latencies[len(latencies)-1],
		AvgLatency:         totalLatency / time.Duration(len(results)),
		RPS:                actualRPS,
	}
}

// checkGates checks if the benchmark results meet the required gates
func checkGates(summary SummaryStats, config BenchmarkConfig) (bool, []string) {
	var failures []string

	// P95 latency gate (≤20ms for weekly, ≤22ms for PR)
	latencyGate := 20 * time.Millisecond
	if config.Duration < 5*time.Minute {
		latencyGate = 22 * time.Millisecond // More lenient for PR jobs
	}

	if summary.P95Latency > latencyGate {
		failures = append(failures, fmt.Sprintf("P95 latency %.2fms exceeds gate %.2fms",
			float64(summary.P95Latency.Microseconds())/1000,
			float64(latencyGate.Microseconds())/1000))
	}

	// Success rate gate (≥99.5%)
	if summary.SuccessRate < 99.5 {
		failures = append(failures, fmt.Sprintf("Success rate %.2f%% below 99.5%%", summary.SuccessRate))
	}

	// RPS gate (within 10% of target)
	targetRPS := float64(config.TargetRPS)
	if summary.RPS < targetRPS*0.9 {
		failures = append(failures, fmt.Sprintf("Actual RPS %.2f below target %.2f", summary.RPS, targetRPS))
	}

	return len(failures) == 0, failures
}

func main() {
	var config BenchmarkConfig

	flag.IntVar(&config.TargetRPS, "rps", 5000, "Target requests per second")
	flag.DurationVar(&config.Duration, "duration", 10*time.Minute, "Benchmark duration")
	flag.IntVar(&config.Concurrency, "concurrency", 50, "Number of concurrent workers")
	flag.StringVar(&config.Endpoint, "endpoint", "http://localhost:8080/proof", "ProofMeter endpoint")
	flag.DurationVar(&config.Timeout, "timeout", 30*time.Second, "Request timeout")
	flag.StringVar(&config.OutputFile, "output", "benchmark_results.json", "Output file")
	flag.Int64Var(&config.Seed, "seed", time.Now().UnixNano(), "Random seed")
	flag.Parse()

	// Set random seed for deterministic results
	rand.Seed(config.Seed)

	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), config.Duration)
	defer cancel()

	// Create results channel
	results := make(chan LatencyResult, config.TargetRPS*10)

	// Start workers
	var wg sync.WaitGroup
	for i := 0; i < config.Concurrency; i++ {
		worker := NewWorker(i, config, results, &wg)
		wg.Add(1)
		go worker.Run(ctx)
	}

	// Collect results
	var allResults []LatencyResult
	go func() {
		for result := range results {
			allResults = append(allResults, result)
		}
	}()

	// Wait for benchmark to complete
	wg.Wait()
	close(results)

	// Calculate summary
	summary := calculateSummary(allResults, config.Duration)

	// Create benchmark result
	benchResult := BenchmarkResult{
		Config:    config,
		Results:   allResults,
		Summary:   summary,
		Timestamp: time.Now(),
	}

	// Check gates
	gatesPassed, failures := checkGates(summary, config)

	// Print results
	fmt.Printf("🔍 ProofMeter Benchmark Results\n")
	fmt.Printf("================================\n")
	fmt.Printf("Duration: %v\n", config.Duration)
	fmt.Printf("Target RPS: %d\n", config.TargetRPS)
	fmt.Printf("Actual RPS: %.2f\n", summary.RPS)
	fmt.Printf("Total Requests: %d\n", summary.TotalRequests)
	fmt.Printf("Successful: %d\n", summary.SuccessfulRequests)
	fmt.Printf("Failed: %d\n", summary.FailedRequests)
	fmt.Printf("Success Rate: %.2f%%\n", summary.SuccessRate)
	fmt.Printf("\nLatency Statistics:\n")
	fmt.Printf("  P50: %.2fms\n", float64(summary.P50Latency.Microseconds())/1000)
	fmt.Printf("  P95: %.2fms\n", float64(summary.P95Latency.Microseconds())/1000)
	fmt.Printf("  P99: %.2fms\n", float64(summary.P99Latency.Microseconds())/1000)
	fmt.Printf("  Min: %.2fms\n", float64(summary.MinLatency.Microseconds())/1000)
	fmt.Printf("  Max: %.2fms\n", float64(summary.MaxLatency.Microseconds())/1000)
	fmt.Printf("  Avg: %.2fms\n", float64(summary.AvgLatency.Microseconds())/1000)

	if gatesPassed {
		fmt.Printf("\n✅ All gates passed!\n")
	} else {
		fmt.Printf("\n❌ Some gates failed:\n")
		for _, failure := range failures {
			fmt.Printf("  - %s\n", failure)
		}
	}

	// Save results to file
	jsonData, err := json.MarshalIndent(benchResult, "", "  ")
	if err != nil {
		log.Fatalf("Failed to marshal results: %v", err)
	}

	if err := os.WriteFile(config.OutputFile, jsonData, 0644); err != nil {
		log.Fatalf("Failed to write results file: %v", err)
	}

	fmt.Printf("\n📊 Results saved to %s\n", config.OutputFile)

	// Exit with appropriate code
	if !gatesPassed {
		os.Exit(1)
	}
}
