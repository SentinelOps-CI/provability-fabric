// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"archive/zip"
	"context"
	"crypto/sha256"
	"database/sql"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
	_ "github.com/lib/pq"
)

// CertV1 represents a CERT-V1 certificate
type CertV1 struct {
	BundleID        string                 `json:"bundle_id"`
	PolicyHash      string                 `json:"policy_hash"`
	ProofHash       string                 `json:"proof_hash"`
	AutomataHash    string                 `json:"automata_hash"`
	LabelerHash     string                 `json:"labeler_hash"`
	NIClaim         string                 `json:"ni_claim"`
	NIMonitor       string                 `json:"ni_monitor"` // "inapplicable" | "accept" | "reject" | "error"
	SidecarBuild    string                 `json:"sidecar_build"`
	AttestationRef  string                 `json:"attestation_ref,omitempty"`
	Extensions      map[string]interface{} `json:"extensions,omitempty"`
	Timestamp       time.Time              `json:"timestamp"`
	TenantID        string                 `json:"tenant_id"`
	SessionID       string                 `json:"session_id"`
	Morph           *MorphInfo             `json:"morph,omitempty"`
}

// MorphInfo contains Morph execution environment details
type MorphInfo struct {
	EnvSnapshotDigest string `json:"env_snapshot_digest"`
	BranchID          string `json:"branch_id"`
	BaseImage         string `json:"base_image"`
	MorphVMID         string `json:"morphvm_id,omitempty"`
}

// CertSearchRequest represents certificate search parameters
type CertSearchRequest struct {
	TenantID     string    `json:"tenant_id,omitempty"`
	PolicyHash   string    `json:"policy_hash,omitempty"`
	SessionID    string    `json:"session_id,omitempty"`
	StartTime    time.Time `json:"start_time,omitempty"`
	EndTime      time.Time `json:"end_time,omitempty"`
	NIMonitor    string    `json:"ni_monitor,omitempty"`
	Limit        int       `json:"limit,omitempty"`
	Offset       int       `json:"offset,omitempty"`
}

// CertSearchResponse represents search results
type CertSearchResponse struct {
	Certificates []CertV1 `json:"certificates"`
	Total        int      `json:"total"`
	Limit        int      `json:"limit"`
	Offset       int      `json:"offset"`
}

// CompliancePacket represents a compliance export
type CompliancePacket struct {
	PacketID      string    `json:"packet_id"`
	GeneratedAt   time.Time `json:"generated_at"`
	TenantID      string    `json:"tenant_id"`
	PolicyHash    string    `json:"policy_hash"`
	StartTime     time.Time `json:"start_time"`
	EndTime       time.Time `json:"end_time"`
	Certificates  []CertV1  `json:"certificates"`
	AuditProof    string    `json:"audit_proof"`
	ReplayResults []string  `json:"replay_results"`
	Conformance   string    `json:"conformance"`
}

// EvidenceService handles CERT-V1 storage, validation, and compliance
type EvidenceService struct {
	db          *sql.DB
	storagePath string
	schemaData  []byte
}

// NewEvidenceService creates a new evidence service instance
func NewEvidenceService() (*EvidenceService, error) {
	// Database connection
	dbURL := os.Getenv("DATABASE_URL")
	if dbURL == "" {
		dbURL = "postgres://postgres:password@localhost:5432/evidence?sslmode=disable"
	}
	
	db, err := sql.Open("postgres", dbURL)
	if err != nil {
		return nil, fmt.Errorf("failed to connect to database: %w", err)
	}
	
	// Test connection
	if err := db.Ping(); err != nil {
		log.Printf("Warning: Database connection failed: %v", err)
		// Continue without database for development
	}
	
	// Storage path
	storagePath := os.Getenv("EVIDENCE_STORAGE_PATH")
	if storagePath == "" {
		storagePath = "/tmp/evidence"
	}
	os.MkdirAll(storagePath, 0755)
	
	// Load CERT-V1 schema
	schemaPath := "external/CERT-V1/schema/cert-v1.schema.json"
	schemaData, err := os.ReadFile(schemaPath)
	if err != nil {
		log.Printf("Warning: Could not load CERT-V1 schema: %v", err)
		schemaData = []byte(`{"type": "object"}`) // Fallback schema
	}
	
	service := &EvidenceService{
		db:          db,
		storagePath: storagePath,
		schemaData:  schemaData,
	}
	
	// Initialize database schema
	if err := service.initializeSchema(); err != nil {
		log.Printf("Warning: Could not initialize database schema: %v", err)
	}
	
	return service, nil
}

// initializeSchema creates database tables
func (s *EvidenceService) initializeSchema() error {
	if s.db == nil {
		return nil // Skip if no database
	}
	
	schema := `
	CREATE TABLE IF NOT EXISTS certificates (
		id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
		bundle_id VARCHAR(255) NOT NULL,
		policy_hash VARCHAR(64) NOT NULL,
		proof_hash VARCHAR(64) NOT NULL,
		automata_hash VARCHAR(64) NOT NULL,
		labeler_hash VARCHAR(64) NOT NULL,
		ni_claim VARCHAR(255) NOT NULL,
		ni_monitor VARCHAR(20) NOT NULL,
		sidecar_build VARCHAR(255) NOT NULL,
		tenant_id VARCHAR(255) NOT NULL,
		session_id VARCHAR(255) NOT NULL,
		timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
		cert_data JSONB NOT NULL,
		created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
	);
	
	CREATE INDEX IF NOT EXISTS idx_certificates_tenant_id ON certificates(tenant_id);
	CREATE INDEX IF NOT EXISTS idx_certificates_policy_hash ON certificates(policy_hash);
	CREATE INDEX IF NOT EXISTS idx_certificates_session_id ON certificates(session_id);
	CREATE INDEX IF NOT EXISTS idx_certificates_timestamp ON certificates(timestamp);
	CREATE INDEX IF NOT EXISTS idx_certificates_ni_monitor ON certificates(ni_monitor);
	
	-- Row Level Security for multi-tenant isolation
	ALTER TABLE certificates ENABLE ROW LEVEL SECURITY;
	
	CREATE POLICY IF NOT EXISTS tenant_isolation ON certificates
		FOR ALL TO ALL
		USING (tenant_id = current_setting('app.current_tenant', true));
	`
	
	_, err := s.db.Exec(schema)
	return err
}

// StoreCertificate validates and stores a CERT-V1 certificate
func (s *EvidenceService) StoreCertificate(ctx context.Context, cert CertV1) error {
	// Validate certificate against CERT-V1 schema
	if err := s.validateCertificate(cert); err != nil {
		return fmt.Errorf("certificate validation failed: %w", err)
	}
	
	// Store in database
	if s.db != nil {
		if err := s.storeCertInDB(cert); err != nil {
			log.Printf("Warning: Database storage failed: %v", err)
		}
	}
	
	// Store in filesystem
	if err := s.storeCertInFS(cert); err != nil {
		return fmt.Errorf("filesystem storage failed: %w", err)
	}
	
	return nil
}

// SearchCertificates searches for certificates based on criteria
func (s *EvidenceService) SearchCertificates(ctx context.Context, req CertSearchRequest) (*CertSearchResponse, error) {
	// Set defaults
	if req.Limit == 0 {
		req.Limit = 100
	}
	if req.Limit > 1000 {
		req.Limit = 1000
	}
	
	var certificates []CertV1
	var total int
	
	if s.db != nil {
		// Database search
		certs, count, err := s.searchCertsInDB(req)
		if err != nil {
			log.Printf("Database search failed, falling back to filesystem: %v", err)
			return s.searchCertsInFS(req)
		}
		certificates = certs
		total = count
	} else {
		// Filesystem search fallback
		return s.searchCertsInFS(req)
	}
	
	return &CertSearchResponse{
		Certificates: certificates,
		Total:        total,
		Limit:        req.Limit,
		Offset:       req.Offset,
	}, nil
}

// BuildCompliancePacket creates a compliance export package
func (s *EvidenceService) BuildCompliancePacket(ctx context.Context, req CertSearchRequest) (*CompliancePacket, error) {
	// Search for relevant certificates
	searchResp, err := s.SearchCertificates(ctx, req)
	if err != nil {
		return nil, err
	}
	
	// Generate audit proof
	auditProof, err := s.generateAuditProof(searchResp.Certificates)
	if err != nil {
		return nil, err
	}
	
	// Generate conformance report
	conformance := s.generateConformanceReport(searchResp.Certificates)
	
	packet := &CompliancePacket{
		PacketID:      uuid.New().String(),
		GeneratedAt:   time.Now(),
		TenantID:      req.TenantID,
		PolicyHash:    req.PolicyHash,
		StartTime:     req.StartTime,
		EndTime:       req.EndTime,
		Certificates:  searchResp.Certificates,
		AuditProof:    auditProof,
		ReplayResults: []string{}, // Would be populated from replay service
		Conformance:   conformance,
	}
	
	return packet, nil
}

// validateCertificate validates against CERT-V1 schema
func (s *EvidenceService) validateCertificate(cert CertV1) error {
	// Simplified validation - in production would use JSON schema validator
	if cert.BundleID == "" {
		return fmt.Errorf("missing bundle_id")
	}
	if cert.PolicyHash == "" {
		return fmt.Errorf("missing policy_hash")
	}
	if cert.ProofHash == "" {
		return fmt.Errorf("missing proof_hash")
	}
	if cert.AutomataHash == "" {
		return fmt.Errorf("missing automata_hash")
	}
	if cert.LabelerHash == "" {
		return fmt.Errorf("missing labeler_hash")
	}
	if cert.NIClaim == "" {
		return fmt.Errorf("missing ni_claim")
	}
	if cert.NIMonitor == "" {
		return fmt.Errorf("missing ni_monitor")
	}
	if cert.SidecarBuild == "" {
		return fmt.Errorf("missing sidecar_build")
	}
	
	// Validate ni_monitor values
	validNIMonitor := []string{"inapplicable", "accept", "reject", "error"}
	valid := false
	for _, v := range validNIMonitor {
		if cert.NIMonitor == v {
			valid = true
			break
		}
	}
	if !valid {
		return fmt.Errorf("invalid ni_monitor value: %s", cert.NIMonitor)
	}
	
	return nil
}

// storeCertInDB stores certificate in PostgreSQL
func (s *EvidenceService) storeCertInDB(cert CertV1) error {
	query := `
		INSERT INTO certificates (
			bundle_id, policy_hash, proof_hash, automata_hash, labeler_hash,
			ni_claim, ni_monitor, sidecar_build, tenant_id, session_id,
			timestamp, cert_data
		) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)
	`
	
	certData, err := json.Marshal(cert)
	if err != nil {
		return err
	}
	
	_, err = s.db.Exec(query,
		cert.BundleID, cert.PolicyHash, cert.ProofHash, cert.AutomataHash,
		cert.LabelerHash, cert.NIClaim, cert.NIMonitor, cert.SidecarBuild,
		cert.TenantID, cert.SessionID, cert.Timestamp, string(certData),
	)
	
	return err
}

// storeCertInFS stores certificate in filesystem
func (s *EvidenceService) storeCertInFS(cert CertV1) error {
	// Create directory structure: evidence/certs/{tenant}/{session}/
	certDir := filepath.Join(s.storagePath, "certs", cert.TenantID, cert.SessionID)
	if err := os.MkdirAll(certDir, 0755); err != nil {
		return err
	}
	
	// Generate filename with timestamp
	filename := fmt.Sprintf("%d_%s.cert.json", cert.Timestamp.Unix(), uuid.New().String()[:8])
	certPath := filepath.Join(certDir, filename)
	
	// Write certificate
	certData, err := json.MarshalIndent(cert, "", "  ")
	if err != nil {
		return err
	}
	
	return os.WriteFile(certPath, certData, 0644)
}

// searchCertsInDB searches certificates in database
func (s *EvidenceService) searchCertsInDB(req CertSearchRequest) ([]CertV1, int, error) {
	// Build dynamic query
	var conditions []string
	var args []interface{}
	argIndex := 1
	
	if req.TenantID != "" {
		conditions = append(conditions, fmt.Sprintf("tenant_id = $%d", argIndex))
		args = append(args, req.TenantID)
		argIndex++
	}
	
	if req.PolicyHash != "" {
		conditions = append(conditions, fmt.Sprintf("policy_hash = $%d", argIndex))
		args = append(args, req.PolicyHash)
		argIndex++
	}
	
	if req.SessionID != "" {
		conditions = append(conditions, fmt.Sprintf("session_id = $%d", argIndex))
		args = append(args, req.SessionID)
		argIndex++
	}
	
	if !req.StartTime.IsZero() {
		conditions = append(conditions, fmt.Sprintf("timestamp >= $%d", argIndex))
		args = append(args, req.StartTime)
		argIndex++
	}
	
	if !req.EndTime.IsZero() {
		conditions = append(conditions, fmt.Sprintf("timestamp <= $%d", argIndex))
		args = append(args, req.EndTime)
		argIndex++
	}
	
	if req.NIMonitor != "" {
		conditions = append(conditions, fmt.Sprintf("ni_monitor = $%d", argIndex))
		args = append(args, req.NIMonitor)
		argIndex++
	}
	
	whereClause := ""
	if len(conditions) > 0 {
		whereClause = "WHERE " + strings.Join(conditions, " AND ")
	}
	
	// Count query
	countQuery := fmt.Sprintf("SELECT COUNT(*) FROM certificates %s", whereClause)
	var total int
	err := s.db.QueryRow(countQuery, args...).Scan(&total)
	if err != nil {
		return nil, 0, err
	}
	
	// Data query
	dataQuery := fmt.Sprintf(`
		SELECT cert_data FROM certificates %s 
		ORDER BY timestamp DESC 
		LIMIT $%d OFFSET $%d
	`, whereClause, argIndex, argIndex+1)
	
	args = append(args, req.Limit, req.Offset)
	
	rows, err := s.db.Query(dataQuery, args...)
	if err != nil {
		return nil, 0, err
	}
	defer rows.Close()
	
	var certificates []CertV1
	for rows.Next() {
		var certData string
		if err := rows.Scan(&certData); err != nil {
			continue
		}
		
		var cert CertV1
		if err := json.Unmarshal([]byte(certData), &cert); err != nil {
			continue
		}
		
		certificates = append(certificates, cert)
	}
	
	return certificates, total, nil
}

// searchCertsInFS searches certificates in filesystem (fallback)
func (s *EvidenceService) searchCertsInFS(req CertSearchRequest) (*CertSearchResponse, error) {
	var certificates []CertV1
	
	certsDir := filepath.Join(s.storagePath, "certs")
	
	err := filepath.Walk(certsDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // Continue on errors
		}
		
		if !strings.HasSuffix(path, ".cert.json") {
			return nil
		}
		
		// Read certificate
		data, err := os.ReadFile(path)
		if err != nil {
			return nil
		}
		
		var cert CertV1
		if err := json.Unmarshal(data, &cert); err != nil {
			return nil
		}
		
		// Apply filters
		if req.TenantID != "" && cert.TenantID != req.TenantID {
			return nil
		}
		if req.PolicyHash != "" && cert.PolicyHash != req.PolicyHash {
			return nil
		}
		if req.SessionID != "" && cert.SessionID != req.SessionID {
			return nil
		}
		if req.NIMonitor != "" && cert.NIMonitor != req.NIMonitor {
			return nil
		}
		if !req.StartTime.IsZero() && cert.Timestamp.Before(req.StartTime) {
			return nil
		}
		if !req.EndTime.IsZero() && cert.Timestamp.After(req.EndTime) {
			return nil
		}
		
		certificates = append(certificates, cert)
		return nil
	})
	
	if err != nil {
		return nil, err
	}
	
	// Apply pagination
	total := len(certificates)
	start := req.Offset
	end := req.Offset + req.Limit
	
	if start > total {
		start = total
	}
	if end > total {
		end = total
	}
	
	if start < end {
		certificates = certificates[start:end]
	} else {
		certificates = []CertV1{}
	}
	
	return &CertSearchResponse{
		Certificates: certificates,
		Total:        total,
		Limit:        req.Limit,
		Offset:       req.Offset,
	}, nil
}

// generateAuditProof creates cryptographic audit proof
func (s *EvidenceService) generateAuditProof(certs []CertV1) (string, error) {
	// Generate hash chain of certificates
	var hashes []string
	for _, cert := range certs {
		certData, _ := json.Marshal(cert)
		hash := fmt.Sprintf("%x", sha256.Sum256(certData))
		hashes = append(hashes, hash)
	}
	
	// Create audit proof structure
	auditProof := map[string]interface{}{
		"certificate_count": len(certs),
		"hash_chain":       hashes,
		"root_hash":        s.calculateRootHash(hashes),
		"generated_at":     time.Now().Unix(),
	}
	
	proofData, err := json.Marshal(auditProof)
	if err != nil {
		return "", err
	}
	
	return string(proofData), nil
}

// generateConformanceReport creates conformance documentation
func (s *EvidenceService) generateConformanceReport(certs []CertV1) string {
	var report strings.Builder
	
	report.WriteString("# Compliance Conformance Report\n\n")
	report.WriteString(fmt.Sprintf("Generated: %s\n", time.Now().Format(time.RFC3339)))
	report.WriteString(fmt.Sprintf("Total Certificates: %d\n\n", len(certs)))
	
	// Analyze certificate distribution
	niMonitorCounts := make(map[string]int)
	policyHashes := make(map[string]int)
	
	for _, cert := range certs {
		niMonitorCounts[cert.NIMonitor]++
		policyHashes[cert.PolicyHash]++
	}
	
	report.WriteString("## Non-Interference Monitor Results\n\n")
	for status, count := range niMonitorCounts {
		report.WriteString(fmt.Sprintf("- %s: %d certificates\n", status, count))
	}
	
	report.WriteString("\n## Policy Distribution\n\n")
	for hash, count := range policyHashes {
		report.WriteString(fmt.Sprintf("- Policy %s: %d certificates\n", hash[:16], count))
	}
	
	// Compliance summary
	report.WriteString("\n## Compliance Summary\n\n")
	acceptCount := niMonitorCounts["accept"]
	totalCount := len(certs)
	
	if totalCount > 0 {
		complianceRate := float64(acceptCount) / float64(totalCount) * 100
		report.WriteString(fmt.Sprintf("- Compliance Rate: %.2f%%\n", complianceRate))
		report.WriteString(fmt.Sprintf("- Total Decisions: %d\n", totalCount))
		report.WriteString(fmt.Sprintf("- Accepted: %d\n", acceptCount))
		report.WriteString(fmt.Sprintf("- Rejected: %d\n", niMonitorCounts["reject"]))
		report.WriteString(fmt.Sprintf("- Errors: %d\n", niMonitorCounts["error"]))
	}
	
	return report.String()
}

// calculateRootHash calculates Merkle root of certificate hashes
func (s *EvidenceService) calculateRootHash(hashes []string) string {
	if len(hashes) == 0 {
		return ""
	}
	if len(hashes) == 1 {
		return hashes[0]
	}
	
	// Simple hash combination (in production would use proper Merkle tree)
	combined := strings.Join(hashes, "")
	hash := sha256.Sum256([]byte(combined))
	return fmt.Sprintf("%x", hash)
}

// HTTP handlers
func (s *EvidenceService) storeCertHandler(c *gin.Context) {
	var cert CertV1
	if err := c.ShouldBindJSON(&cert); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	if err := s.StoreCertificate(c.Request.Context(), cert); err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusCreated, gin.H{"status": "stored"})
}

func (s *EvidenceService) searchCertsHandler(c *gin.Context) {
	var req CertSearchRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	resp, err := s.SearchCertificates(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, resp)
}

func (s *EvidenceService) getCertHandler(c *gin.Context) {
	certID := c.Param("id")
	
	// Search by ID (simplified)
	req := CertSearchRequest{
		SessionID: certID,
		Limit:     1,
	}
	
	resp, err := s.SearchCertificates(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	if len(resp.Certificates) == 0 {
		c.JSON(http.StatusNotFound, gin.H{"error": "Certificate not found"})
		return
	}
	
	c.JSON(http.StatusOK, resp.Certificates[0])
}

func (s *EvidenceService) buildPacketHandler(c *gin.Context) {
	var req CertSearchRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	
	packet, err := s.BuildCompliancePacket(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.JSON(http.StatusOK, packet)
}

func (s *EvidenceService) downloadPacketHandler(c *gin.Context) {
	packetID := c.Param("id")
	
	// Create temporary zip file
	zipPath := filepath.Join(s.storagePath, fmt.Sprintf("packet_%s.zip", packetID))
	
	if err := s.createPacketZip(packetID, zipPath); err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}
	
	c.Header("Content-Type", "application/zip")
	c.Header("Content-Disposition", fmt.Sprintf("attachment; filename=compliance_packet_%s.zip", packetID))
	c.File(zipPath)
	
	// Clean up
	go func() {
		time.Sleep(1 * time.Minute)
		os.Remove(zipPath)
	}()
}

func (s *EvidenceService) createPacketZip(packetID, zipPath string) error {
	file, err := os.Create(zipPath)
	if err != nil {
		return err
	}
	defer file.Close()
	
	w := zip.NewWriter(file)
	defer w.Close()
	
	// Add placeholder files (in production would include actual compliance data)
	files := map[string]string{
		"cert.json":        `{"packet_id": "` + packetID + `"}`,
		"audit-proof.json": `{"proof": "placeholder"}`,
		"conformance.md":   "# Conformance Report\n\nPlaceholder content",
	}
	
	for filename, content := range files {
		f, err := w.Create(filename)
		if err != nil {
			return err
		}
		
		_, err = f.Write([]byte(content))
		if err != nil {
			return err
		}
	}
	
	return nil
}

func (s *EvidenceService) healthHandler(c *gin.Context) {
	dbStatus := "disconnected"
	if s.db != nil {
		if err := s.db.Ping(); err == nil {
			dbStatus = "connected"
		}
	}
	
	c.JSON(http.StatusOK, gin.H{
		"status":      "healthy",
		"service":     "evidence-service",
		"version":     "1.0.0",
		"timestamp":   time.Now(),
		"database":    dbStatus,
		"storage":     s.storagePath,
	})
}

func main() {
	// Initialize service
	service, err := NewEvidenceService()
	if err != nil {
		log.Fatalf("Failed to initialize evidence service: %v", err)
	}
	
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
		v1.POST("/evidence/cert", service.storeCertHandler)
		v1.POST("/evidence/search", service.searchCertsHandler)
		v1.GET("/evidence/cert/:id", service.getCertHandler)
		v1.POST("/compliance/packet", service.buildPacketHandler)
		v1.GET("/compliance/packet/:id", service.downloadPacketHandler)
		v1.GET("/health", service.healthHandler)
	}
	
	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8004"
	}
	
	log.Printf("Evidence Service starting on port %s", port)
	log.Fatal(r.Run(":" + port))
}