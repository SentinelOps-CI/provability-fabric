// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"math/rand"
	"net/http"
	"os"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
)

// PolicyDiffService handles blast-radius analysis on policy diffs
type PolicyDiffService struct {
	evidenceService *EvidenceServiceClient
	replayService   *ReplayServiceClient
	storagePath     string
}

// EvidenceServiceClient represents a client to the evidence service
type EvidenceServiceClient struct {
	BaseURL string
}

// ReplayServiceClient represents a client to the replay service
type ReplayServiceClient struct {
	BaseURL string
}

// PolicyDiffRequest represents a request to analyze policy differences
type PolicyDiffRequest struct {
	PullRequestID  string    `json:"pull_request_id" binding:"required"`
	BasePolicyHash string    `json:"base_policy_hash" binding:"required"`
	HeadPolicyHash string    `json:"head_policy_hash" binding:"required"`
	SampleSize     int       `json:"sample_size,omitempty"`
	TenantID       string    `json:"tenant_id,omitempty"`
	StartTime      time.Time `json:"start_time,omitempty"`
	EndTime        time.Time `json:"end_time,omitempty"`
	IncludeReplay  bool      `json:"include_replay,omitempty"`
}

// PolicyDiffResponse represents the analysis results
type PolicyDiffResponse struct {
	AnalysisID      string                `json:"analysis_id"`
	PullRequestID   string                `json:"pull_request_id"`
	BasePolicyHash  string                `json:"base_policy_hash"`
	HeadPolicyHash  string                `json:"head_policy_hash"`
	AnalysisTime    time.Time             `json:"analysis_time"`
	DecisionChanges DecisionChangeSummary `json:"decision_changes"`
	ReplayResults   []ReplayResult        `json:"replay_results,omitempty"`
	Recommendations []string              `json:"recommendations"`
	RiskAssessment  RiskAssessment        `json:"risk_assessment"`
}

// DecisionChangeSummary summarizes decision changes
type DecisionChangeSummary struct {
	TotalDecisions   int              `json:"total_decisions"`
	ChangedDecisions int              `json:"changed_decisions"`
	ChangePercentage float64          `json:"change_percentage"`
	ChangeCategories map[string]int   `json:"change_categories"`
	ChangeBreakdown  []DecisionChange `json:"change_breakdown"`
	AffectedTenants  []string         `json:"affected_tenants"`
	AffectedSessions []string         `json:"affected_sessions"`
}

// DecisionChange represents a specific decision change
type DecisionChange struct {
	CertificateID    string    `json:"certificate_id"`
	SessionID        string    `json:"session_id"`
	TenantID         string    `json:"tenant_id"`
	OriginalDecision string    `json:"original_decision"`
	NewDecision      string    `json:"new_decision"`
	ChangeType       string    `json:"change_type"` // "permit_to_deny", "deny_to_permit", "other"
	Confidence       float64   `json:"confidence"`
	Timestamp        time.Time `json:"timestamp"`
	Reason           string    `json:"reason"`
}

// ReplayResult represents the result of a replay analysis
type ReplayResult struct {
	CertificateID      string  `json:"certificate_id"`
	ReplayJobID        string  `json:"replay_job_id"`
	LowViewMatchPct    float64 `json:"low_view_match_pct"`
	FirstMismatchIndex int     `json:"first_mismatch_index"`
	DriftDetected      bool    `json:"drift_detected"`
	Status             string  `json:"status"`
	ErrorMessage       string  `json:"error_message,omitempty"`
}

// RiskAssessment provides risk analysis
type RiskAssessment struct {
	OverallRisk      string       `json:"overall_risk"` // "low", "medium", "high", "critical"
	RiskScore        float64      `json:"risk_score"`   // 0.0 to 1.0
	RiskFactors      []RiskFactor `json:"risk_factors"`
	MitigationAdvice []string     `json:"mitigation_advice"`
	ApprovalRequired bool         `json:"approval_required"`
}

// RiskFactor represents a specific risk factor
type RiskFactor struct {
	Factor      string  `json:"factor"`
	Description string  `json:"description"`
	Severity    string  `json:"severity"` // "low", "medium", "high", "critical"
	Impact      float64 `json:"impact"`   // 0.0 to 1.0
}

// NewPolicyDiffService creates a new policy diff service
func NewPolicyDiffService() *PolicyDiffService {
	storagePath := os.Getenv("POLICY_DIFF_STORAGE_PATH")
	if storagePath == "" {
		storagePath = "/tmp/policy-diffs"
	}
	os.MkdirAll(storagePath, 0755)

	return &PolicyDiffService{
		evidenceService: &EvidenceServiceClient{
			BaseURL: os.Getenv("EVIDENCE_SERVICE_URL"),
		},
		replayService: &ReplayServiceClient{
			BaseURL: os.Getenv("REPLAY_SERVICE_URL"),
		},
		storagePath: storagePath,
	}
}

// AnalyzePolicyDiff analyzes the blast radius of policy changes
func (s *PolicyDiffService) AnalyzePolicyDiff(ctx context.Context, req PolicyDiffRequest) (*PolicyDiffResponse, error) {
	analysisID := uuid.New().String()

	// Set default sample size
	if req.SampleSize == 0 {
		req.SampleSize = 1000
	}

	// Get certificates for both policy versions
	baseCerts, err := s.getCertificatesForPolicy(req.BasePolicyHash, req.SampleSize, req.TenantID, req.StartTime, req.EndTime)
	if err != nil {
		return nil, fmt.Errorf("failed to get base certificates: %w", err)
	}

	headCerts, err := s.getCertificatesForPolicy(req.HeadPolicyHash, req.SampleSize, req.TenantID, req.StartTime, req.EndTime)
	if err != nil {
		return nil, fmt.Errorf("failed to get head certificates: %w", err)
	}

	// Analyze decision changes
	decisionChanges, err := s.analyzeDecisionChanges(baseCerts, headCerts)
	if err != nil {
		return nil, fmt.Errorf("failed to analyze decision changes: %w", err)
	}

	// Perform replay analysis if requested
	var replayResults []ReplayResult
	if req.IncludeReplay {
		replayResults, err = s.performReplayAnalysis(decisionChanges)
		if err != nil {
			log.Printf("Replay analysis failed: %v", err)
			// Continue without replay results
		}
	}

	// Assess risk
	riskAssessment := s.assessRisk(decisionChanges, replayResults)

	// Generate recommendations
	recommendations := s.generateRecommendations(decisionChanges, riskAssessment)

	response := &PolicyDiffResponse{
		AnalysisID:      analysisID,
		PullRequestID:   req.PullRequestID,
		BasePolicyHash:  req.BasePolicyHash,
		HeadPolicyHash:  req.HeadPolicyHash,
		AnalysisTime:    time.Now(),
		DecisionChanges: decisionChanges,
		ReplayResults:   replayResults,
		Recommendations: recommendations,
		RiskAssessment:  riskAssessment,
	}

	// Store analysis results
	if err := s.storeAnalysisResults(response); err != nil {
		log.Printf("Failed to store analysis results: %v", err)
	}

	return response, nil
}

// getCertificatesForPolicy retrieves certificates for a specific policy
func (s *PolicyDiffService) getCertificatesForPolicy(policyHash string, sampleSize int, tenantID string, startTime, endTime time.Time) ([]Certificate, error) {
	// This would make an actual API call to the evidence service
	// For now, return mock data
	return s.generateMockCertificates(policyHash, sampleSize, tenantID), nil
}

// generateMockCertificates generates mock certificate data
func (s *PolicyDiffService) generateMockCertificates(policyHash string, count int, tenantID string) []Certificate {
	certs := make([]Certificate, count)
	for i := 0; i < count; i++ {
		certs[i] = Certificate{
			BundleID:   fmt.Sprintf("bundle-%d", i),
			SessionID:  fmt.Sprintf("session-%d", i),
			TenantID:   tenantID,
			PolicyHash: policyHash,
			NIMonitor:  s.getRandomNIMonitor(),
			ReasonCode: s.getRandomReasonCode(),
			Timestamp:  time.Now().Add(-time.Duration(i) * time.Hour),
		}
	}
	return certs
}

// getRandomNIMonitor returns a random NI monitor value
func (s *PolicyDiffService) getRandomNIMonitor() string {
	values := []string{"accept", "reject", "inapplicable", "error"}
	return values[rand.Intn(len(values))]
}

// getRandomReasonCode returns a random reason code
func (s *PolicyDiffService) getRandomReasonCode() string {
	codes := []string{"PERMIT", "DENY", "ERROR", "TIMEOUT"}
	return codes[rand.Intn(len(codes))]
}

// Certificate represents a certificate for analysis
type Certificate struct {
	BundleID   string    `json:"bundle_id"`
	SessionID  string    `json:"session_id"`
	TenantID   string    `json:"tenant_id"`
	PolicyHash string    `json:"policy_hash"`
	NIMonitor  string    `json:"ni_monitor"`
	ReasonCode string    `json:"reason_code"`
	Timestamp  time.Time `json:"timestamp"`
}

// analyzeDecisionChanges analyzes changes between base and head certificates
func (s *PolicyDiffService) analyzeDecisionChanges(baseCerts, headCerts []Certificate) (DecisionChangeSummary, error) {
	// Create maps for efficient lookup
	baseMap := make(map[string]Certificate)
	for _, cert := range baseCerts {
		key := s.getCertificateKey(cert)
		baseMap[key] = cert
	}

	var changes []DecisionChange
	changeCategories := make(map[string]int)
	affectedTenants := make(map[string]bool)
	affectedSessions := make(map[string]bool)

	// Compare certificates
	for _, headCert := range headCerts {
		key := s.getCertificateKey(headCert)
		baseCert, exists := baseMap[key]

		if !exists {
			// New certificate
			change := DecisionChange{
				CertificateID:    headCert.BundleID,
				SessionID:        headCert.SessionID,
				TenantID:         headCert.TenantID,
				OriginalDecision: "N/A",
				NewDecision:      headCert.NIMonitor,
				ChangeType:       "new_certificate",
				Confidence:       1.0,
				Timestamp:        headCert.Timestamp,
				Reason:           "New certificate in head policy",
			}
			changes = append(changes, change)
			changeCategories["new_certificate"]++
		} else {
			// Compare decisions
			if baseCert.NIMonitor != headCert.NIMonitor {
				changeType := s.determineChangeType(baseCert.NIMonitor, headCert.NIMonitor)
				confidence := s.calculateChangeConfidence(baseCert, headCert)

				change := DecisionChange{
					CertificateID:    headCert.BundleID,
					SessionID:        headCert.SessionID,
					TenantID:         headCert.TenantID,
					OriginalDecision: baseCert.NIMonitor,
					NewDecision:      headCert.NIMonitor,
					ChangeType:       changeType,
					Confidence:       confidence,
					Timestamp:        headCert.Timestamp,
					Reason:           s.generateChangeReason(baseCert, headCert),
				}
				changes = append(changes, change)
				changeCategories[changeType]++
			}
		}

		affectedTenants[headCert.TenantID] = true
		affectedSessions[headCert.SessionID] = true
	}

	// Convert maps to slices
	var tenantList []string
	for tenant := range affectedTenants {
		tenantList = append(tenantList, tenant)
	}

	var sessionList []string
	for session := range affectedSessions {
		sessionList = append(sessionList, session)
	}

	// Calculate percentages
	totalDecisions := len(headCerts)
	changedDecisions := len(changes)
	changePercentage := 0.0
	if totalDecisions > 0 {
		changePercentage = float64(changedDecisions) / float64(totalDecisions) * 100
	}

	return DecisionChangeSummary{
		TotalDecisions:   totalDecisions,
		ChangedDecisions: changedDecisions,
		ChangePercentage: changePercentage,
		ChangeCategories: changeCategories,
		ChangeBreakdown:  changes,
		AffectedTenants:  tenantList,
		AffectedSessions: sessionList,
	}, nil
}

// getCertificateKey generates a unique key for certificate comparison
func (s *PolicyDiffService) getCertificateKey(cert Certificate) string {
	return fmt.Sprintf("%s:%s", cert.BundleID, cert.SessionID)
}

// determineChangeType determines the type of decision change
func (s *PolicyDiffService) determineChangeType(original, new string) string {
	if original == "accept" && new == "reject" {
		return "permit_to_deny"
	}
	if original == "reject" && new == "accept" {
		return "deny_to_permit"
	}
	if original == "inapplicable" && new != "inapplicable" {
		return "inapplicable_to_decision"
	}
	if original != "inapplicable" && new == "inapplicable" {
		return "decision_to_inapplicable"
	}
	return "other"
}

// calculateChangeConfidence calculates confidence in the change
func (s *PolicyDiffService) calculateChangeConfidence(base, head Certificate) float64 {
	// Simple confidence calculation based on time difference and decision types
	timeDiff := head.Timestamp.Sub(base.Timestamp).Hours()

	// Higher confidence for recent changes
	timeConfidence := 1.0
	if timeDiff > 24 {
		timeConfidence = 0.8
	}
	if timeDiff > 168 { // 1 week
		timeConfidence = 0.6
	}

	// Higher confidence for certain decision type changes
	decisionConfidence := 0.5
	if (base.NIMonitor == "accept" && head.NIMonitor == "reject") ||
		(base.NIMonitor == "reject" && head.NIMonitor == "accept") {
		decisionConfidence = 0.9
	}

	return (timeConfidence + decisionConfidence) / 2
}

// generateChangeReason generates a human-readable reason for the change
func (s *PolicyDiffService) generateChangeReason(base, head Certificate) string {
	changeType := s.determineChangeType(base.NIMonitor, head.NIMonitor)

	switch changeType {
	case "permit_to_deny":
		return "Policy change resulted in previously allowed action being denied"
	case "deny_to_permit":
		return "Policy change resulted in previously denied action being allowed"
	case "inapplicable_to_decision":
		return "Policy change made previously inapplicable action subject to decision"
	case "decision_to_inapplicable":
		return "Policy change made previously decided action inapplicable"
	default:
		return "Policy change resulted in decision modification"
	}
}

// performReplayAnalysis performs replay analysis on changed decisions
func (s *PolicyDiffService) performReplayAnalysis(decisionChanges DecisionChangeSummary) ([]ReplayResult, error) {
	var results []ReplayResult

	// Limit to first 10 changes for replay analysis (to avoid overwhelming the system)
	maxReplays := 10
	if len(decisionChanges.ChangeBreakdown) < maxReplays {
		maxReplays = len(decisionChanges.ChangeBreakdown)
	}

	for i := 0; i < maxReplays; i++ {
		change := decisionChanges.ChangeBreakdown[i]

		// Start replay for this certificate
		replayJobID, err := s.startReplayForCertificate(change.CertificateID, change.SessionID)
		if err != nil {
			log.Printf("Failed to start replay for certificate %s: %v", change.CertificateID, err)
			results = append(results, ReplayResult{
				CertificateID: change.CertificateID,
				Status:        "failed",
				ErrorMessage:  err.Error(),
			})
			continue
		}

		// Wait for replay completion and get results
		result, err := s.waitForReplayCompletion(replayJobID)
		if err != nil {
			log.Printf("Failed to get replay results for job %s: %v", replayJobID, err)
			results = append(results, ReplayResult{
				CertificateID: change.CertificateID,
				ReplayJobID:   replayJobID,
				Status:        "failed",
				ErrorMessage:  err.Error(),
			})
			continue
		}

		results = append(results, *result)
	}

	return results, nil
}

// startReplayForCertificate starts a replay for a specific certificate
func (s *PolicyDiffService) startReplayForCertificate(certificateID, sessionID string) (string, error) {
	// This would make an actual API call to the replay service
	// For now, return a mock job ID
	return fmt.Sprintf("replay_%s_%d", certificateID, time.Now().Unix()), nil
}

// waitForReplayCompletion waits for replay completion and returns results
func (s *PolicyDiffService) waitForReplayCompletion(replayJobID string) (*ReplayResult, error) {
	// This would poll the replay service for completion
	// For now, return mock results
	return &ReplayResult{
		CertificateID:      "mock-cert",
		ReplayJobID:        replayJobID,
		LowViewMatchPct:    85.5,
		FirstMismatchIndex: 7,
		DriftDetected:      true,
		Status:             "completed",
	}, nil
}

// assessRisk assesses the risk of the policy changes
func (s *PolicyDiffService) assessRisk(decisionChanges DecisionChangeSummary, replayResults []ReplayResult) RiskAssessment {
	riskScore := 0.0
	var riskFactors []RiskFactor

	// Calculate risk based on change percentage
	changePercentage := decisionChanges.ChangePercentage
	if changePercentage > 50 {
		riskScore += 0.4
		riskFactors = append(riskFactors, RiskFactor{
			Factor:      "high_change_percentage",
			Description: fmt.Sprintf("High percentage of decisions changed: %.1f%%", changePercentage),
			Severity:    "high",
			Impact:      0.4,
		})
	} else if changePercentage > 20 {
		riskScore += 0.2
		riskFactors = append(riskFactors, RiskFactor{
			Factor:      "moderate_change_percentage",
			Description: fmt.Sprintf("Moderate percentage of decisions changed: %.1f%%", changePercentage),
			Severity:    "medium",
			Impact:      0.2,
		})
	}

	// Calculate risk based on permit-to-deny changes
	permitToDenyCount := decisionChanges.ChangeCategories["permit_to_deny"]
	if permitToDenyCount > 0 {
		riskScore += 0.3
		riskFactors = append(riskFactors, RiskFactor{
			Factor:      "permit_to_deny_changes",
			Description: fmt.Sprintf("%d decisions changed from permit to deny", permitToDenyCount),
			Severity:    "high",
			Impact:      0.3,
		})
	}

	// Calculate risk based on replay results
	driftDetectedCount := 0
	for _, result := range replayResults {
		if result.DriftDetected {
			driftDetectedCount++
		}
	}

	if driftDetectedCount > 0 {
		riskScore += 0.2
		riskFactors = append(riskFactors, RiskFactor{
			Factor:      "drift_detected",
			Description: fmt.Sprintf("Drift detected in %d replay analyses", driftDetectedCount),
			Severity:    "medium",
			Impact:      0.2,
		})
	}

	// Determine overall risk level
	overallRisk := "low"
	if riskScore >= 0.7 {
		overallRisk = "critical"
	} else if riskScore >= 0.5 {
		overallRisk = "high"
	} else if riskScore >= 0.3 {
		overallRisk = "medium"
	}

	// Generate mitigation advice
	var mitigationAdvice []string
	if changePercentage > 50 {
		mitigationAdvice = append(mitigationAdvice, "Consider rolling out changes gradually")
	}
	if permitToDenyCount > 0 {
		mitigationAdvice = append(mitigationAdvice, "Review permit-to-deny changes for business impact")
	}
	if driftDetectedCount > 0 {
		mitigationAdvice = append(mitigationAdvice, "Investigate drift in replay analyses")
	}

	return RiskAssessment{
		OverallRisk:      overallRisk,
		RiskScore:        riskScore,
		RiskFactors:      riskFactors,
		MitigationAdvice: mitigationAdvice,
		ApprovalRequired: riskScore >= 0.5,
	}
}

// generateRecommendations generates recommendations based on the analysis
func (s *PolicyDiffService) generateRecommendations(decisionChanges DecisionChangeSummary, riskAssessment RiskAssessment) []string {
	var recommendations []string

	// Recommendations based on change percentage
	if decisionChanges.ChangePercentage > 30 {
		recommendations = append(recommendations, "Consider implementing a gradual rollout strategy")
	}

	// Recommendations based on change types
	if decisionChanges.ChangeCategories["permit_to_deny"] > 0 {
		recommendations = append(recommendations, "Review all permit-to-deny changes for business impact")
		recommendations = append(recommendations, "Ensure affected users are notified of access changes")
	}

	if decisionChanges.ChangeCategories["deny_to_permit"] > 0 {
		recommendations = append(recommendations, "Verify that deny-to-permit changes align with security requirements")
	}

	// Recommendations based on risk assessment
	if riskAssessment.RiskScore >= 0.7 {
		recommendations = append(recommendations, "Require additional approval before deployment")
		recommendations = append(recommendations, "Consider running additional tests")
	}

	// General recommendations
	recommendations = append(recommendations, "Monitor system behavior after deployment")
	recommendations = append(recommendations, "Set up alerts for unexpected decision patterns")

	return recommendations
}

// storeAnalysisResults stores the analysis results
func (s *PolicyDiffService) storeAnalysisResults(response *PolicyDiffResponse) error {
	// Create analysis directory
	analysisDir := fmt.Sprintf("%s/analysis_%s", s.storagePath, response.AnalysisID)
	if err := os.MkdirAll(analysisDir, 0755); err != nil {
		return err
	}

	// Write analysis results to file
	filePath := fmt.Sprintf("%s/analysis_results.json", analysisDir)
	data, err := json.MarshalIndent(response, "", "  ")
	if err != nil {
		return err
	}

	return os.WriteFile(filePath, data, 0644)
}

// HTTP handlers
func (s *PolicyDiffService) analyzePolicyDiffHandler(c *gin.Context) {
	var req PolicyDiffRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}

	response, err := s.AnalyzePolicyDiff(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}

	c.JSON(http.StatusOK, response)
}

func (s *PolicyDiffService) getAnalysisHandler(c *gin.Context) {
	analysisID := c.Param("id")

	// Load analysis results from storage
	filePath := fmt.Sprintf("%s/analysis_%s/analysis_results.json", s.storagePath, analysisID)
	data, err := os.ReadFile(filePath)
	if err != nil {
		c.JSON(http.StatusNotFound, gin.H{"error": "Analysis not found"})
		return
	}

	var response PolicyDiffResponse
	if err := json.Unmarshal(data, &response); err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": "Failed to parse analysis results"})
		return
	}

	c.JSON(http.StatusOK, response)
}

func main() {
	service := NewPolicyDiffService()

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
		v1.POST("/policy-diff/analyze", service.analyzePolicyDiffHandler)
		v1.GET("/policy-diff/analysis/:id", service.getAnalysisHandler)
	}

	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8005"
	}

	log.Printf("Policy Diff Service starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}
