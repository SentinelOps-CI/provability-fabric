// Package policykernel provides pprof profiling endpoints for performance analysis
package policykernel

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/pprof"
	"runtime"
	"strings"
	"time"
)

// PProfServer provides pprof profiling endpoints for the policy kernel
type PProfServer struct {
	addr     string
	server   *http.Server
	enabled  bool
	profiler *PerformanceProfiler
}

// NewPProfServer creates a new pprof server
func NewPProfServer(addr string, profiler *PerformanceProfiler) *PProfServer {
	return &PProfServer{
		addr:     addr,
		profiler: profiler,
		enabled:  true,
	}
}

// Start starts the pprof server
func (s *PProfServer) Start() error {
	if !s.enabled {
		return nil
	}

	mux := http.NewServeMux()

	// Register pprof handlers
	mux.HandleFunc("/debug/pprof/", pprof.Index)
	mux.HandleFunc("/debug/pprof/cmdline", pprof.Cmdline)
	mux.HandleFunc("/debug/pprof/profile", s.handleProfile)
	mux.HandleFunc("/debug/pprof/symbol", pprof.Symbol)
	mux.HandleFunc("/debug/pprof/trace", pprof.Trace)
	mux.HandleFunc("/debug/pprof/goroutine", pprof.Handler("goroutine").ServeHTTP)
	mux.HandleFunc("/debug/pprof/heap", pprof.Handler("heap").ServeHTTP)
	mux.HandleFunc("/debug/pprof/threadcreate", pprof.Handler("threadcreate").ServeHTTP)
	mux.HandleFunc("/debug/pprof/block", pprof.Handler("block").ServeHTTP)
	mux.HandleFunc("/debug/pprof/mutex", pprof.Handler("mutex").ServeHTTP)

	// Custom profiling endpoints
	mux.HandleFunc("/debug/pprof/kernel", s.handleKernelProfile)
	mux.HandleFunc("/debug/pprof/policy", s.handlePolicyProfile)
	mux.HandleFunc("/debug/pprof/cache", s.handleCacheProfile)

	s.server = &http.Server{
		Addr:    s.addr,
		Handler: mux,
	}

	go func() {
		if err := s.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			// Log error but don't fail
			// In production, this should be logged properly
		}
	}()

	return nil
}

// Stop stops the pprof server
func (s *PProfServer) Stop() error {
	if s.server != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		return s.server.Shutdown(ctx)
	}
	return nil
}

// handleProfile handles CPU profiling with configurable duration
func (s *PProfServer) handleProfile(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("Content-Disposition", "attachment; filename=profile.pb.gz")

	// Use the standard pprof profile handler instead of direct CPU profiling
	pprof.Handler("profile").ServeHTTP(w, r)
}

// handleKernelProfile provides kernel-specific performance metrics
func (s *PProfServer) handleKernelProfile(w http.ResponseWriter, r *http.Request) {
	if s.profiler == nil {
		http.Error(w, "Profiler not available", http.StatusServiceUnavailable)
		return
	}

	profile := s.profiler.GetProfile()
	
	w.Header().Set("Content-Type", "application/json")
	
	// Get memory stats
	var memStats runtime.MemStats
	runtime.ReadMemStats(&memStats)
	
	// Return JSON summary of kernel performance
	response := map[string]interface{}{
		"timestamp": time.Now().Unix(),
		"operations": profile.Operations,
		"runtime": map[string]interface{}{
			"goroutines": runtime.NumGoroutine(),
			"memory": map[string]interface{}{
				"alloc":      memStats.Alloc,
				"total_alloc": memStats.TotalAlloc,
				"sys":        memStats.Sys,
				"num_gc":     memStats.NumGC,
			},
		},
	}

	// Encode as JSON
	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(response); err != nil {
		http.Error(w, "Failed to encode profile", http.StatusInternalServerError)
		return
	}
}

// handlePolicyProfile provides policy function performance metrics
func (s *PProfServer) handlePolicyProfile(w http.ResponseWriter, r *http.Request) {
	if s.profiler == nil {
		http.Error(w, "Profiler not available", http.StatusServiceUnavailable)
		return
	}

	profile := s.profiler.GetProfile()
	
	w.Header().Set("Content-Type", "application/json")
	
	// Filter for policy-related operations
	policyOps := make(map[string]*OperationProfile)
	for name, op := range profile.Operations {
		if strings.Contains(strings.ToLower(name), "policy") ||
		   strings.Contains(strings.ToLower(name), "validate") ||
		   strings.Contains(strings.ToLower(name), "approve") {
			policyOps[name] = op
		}
	}

	response := map[string]interface{}{
		"timestamp": time.Now().Unix(),
		"policy_operations": policyOps,
		"summary": map[string]interface{}{
			"total_operations": len(policyOps),
			"total_executions": func() int64 {
				var total int64
				for _, op := range policyOps {
					total += op.Count
				}
				return total
			}(),
		},
	}

	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(response); err != nil {
		http.Error(w, "Failed to encode policy profile", http.StatusInternalServerError)
		return
	}
}

// handleCacheProfile provides cache performance metrics
func (s *PProfServer) handleCacheProfile(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	
	// Get memory stats
	var memStats runtime.MemStats
	runtime.ReadMemStats(&memStats)
	
	// Get cache statistics
	cacheStats := map[string]interface{}{
		"timestamp": time.Now().Unix(),
		"cache": map[string]interface{}{
			"enabled": s.profiler != nil,
			"size":    0, // Would need access to actual cache
			"hits":    0, // Would need access to actual cache
			"misses":  0, // Would need access to actual cache
		},
		"memory": map[string]interface{}{
			"alloc":      memStats.Alloc,
			"total_alloc": memStats.TotalAlloc,
			"sys":        memStats.Sys,
			"num_gc":     memStats.NumGC,
		},
	}

	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(cacheStats); err != nil {
		http.Error(w, "Failed to encode cache profile", http.StatusInternalServerError)
		return
	}
}

// PerformanceSummary provides a summary of performance metrics
type PerformanceSummary struct {
	Timestamp   int64                    `json:"timestamp"`
	Operations  map[string]OperationSummary `json:"operations"`
	Runtime     RuntimeStats             `json:"runtime"`
	Cache       CacheStats               `json:"cache"`
}

// OperationSummary provides summary for a single operation
type OperationSummary struct {
	Count       int64   `json:"count"`
	AverageTime float64 `json:"average_time_ns"`
	MinTime     int64   `json:"min_time_ns"`
	MaxTime     int64   `json:"max_time_ns"`
	P95Time     int64   `json:"p95_time_ns"`
	P99Time     int64   `json:"p99_time_ns"`
}

// RuntimeStats provides runtime statistics
type RuntimeStats struct {
	Goroutines int64  `json:"goroutines"`
	Memory     Memory `json:"memory"`
}

// Memory provides memory statistics
type Memory struct {
	Alloc      uint64 `json:"alloc_bytes"`
	TotalAlloc uint64 `json:"total_alloc_bytes"`
	Sys        uint64 `json:"sys_bytes"`
	NumGC      uint32 `json:"num_gc"`
}

// GetPerformanceSummary returns a comprehensive performance summary
func (s *PProfServer) GetPerformanceSummary() *PerformanceSummary {
	var memStats runtime.MemStats
	runtime.ReadMemStats(&memStats)

	summary := &PerformanceSummary{
		Timestamp:  time.Now().Unix(),
		Operations: make(map[string]OperationSummary),
		Runtime: RuntimeStats{
			Goroutines: int64(runtime.NumGoroutine()),
			Memory: Memory{
				Alloc:      memStats.Alloc,
				TotalAlloc: memStats.TotalAlloc,
				Sys:        memStats.Sys,
				NumGC:      memStats.NumGC,
			},
		},
		Cache: CacheStats{
			HitCount:     0, // Would need access to actual cache
			MissCount:    0, // Would need access to actual cache
			HitRate:      0.0, // Would need access to actual cache
			TotalItems:   0, // Would need access to actual cache
			EvictedCount: 0, // Would need access to actual cache
		},
	}

	// Add operation summaries if profiler is available
	if s.profiler != nil {
		profile := s.profiler.GetProfile()
		for name, op := range profile.Operations {
			summary.Operations[name] = OperationSummary{
				Count:       op.Count,
				AverageTime: float64(op.AverageTime),
				MinTime:     op.MinTime,
				MaxTime:     op.MaxTime,
				P95Time:     op.AverageTime, // Simplified - would need actual p95 calculation
				P99Time:     op.MaxTime,     // Simplified - would need actual p99 calculation
			}
		}
	}

	return summary
}
