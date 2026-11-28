// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"context"
	"crypto/sha256"
	"crypto/subtle"
	"database/sql"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	neturl "net/url"
	"os"
	"path/filepath"
	"strings"
	"time"

	"bytes"
	"crypto/ed25519"
	"crypto/x509"
	"encoding/base64"
	"encoding/pem"
	"io"
	"sort"

	"github.com/gin-gonic/gin"
	"github.com/google/uuid"
	_ "github.com/lib/pq"
)

// Signer defines a pluggable signature backend
// Implementations: file (Ed25519 PEM), kms, vault (stubs)
// Returned signature is base64url-encoded
type Signer interface {
	Sign(message []byte) (string, error)
}

type fileSigner struct {
	priv ed25519.PrivateKey
}

type kmsSigner struct{}

type vaultSigner struct{}

func (s *fileSigner) Sign(message []byte) (string, error) {
	sig := ed25519.Sign(s.priv, message)
	return base64.RawURLEncoding.EncodeToString(sig), nil
}

func (s *kmsSigner) Sign(message []byte) (string, error) {
	return "", fmt.Errorf("kms signer not configured: set CERT_SIGNER_BACKEND=file or integrate KMS externally")
}
func (s *vaultSigner) Sign(message []byte) (string, error) {
	return "", fmt.Errorf("vault signer not configured: set CERT_SIGNER_BACKEND=file or integrate Vault externally")
}

// newSignerFromEnv selects a signer based on CERT_SIGNER_BACKEND
// file: CERT_SIGNER_FILE=/path/to/ed25519.pem
// kms|vault: integrate with your provider (see docs/security/signing-rotation.md)
func newSignerFromEnv() (Signer, error) {
	backend := os.Getenv("CERT_SIGNER_BACKEND")
	switch strings.ToLower(backend) {
	case "file":
		path := os.Getenv("CERT_SIGNER_FILE")
		if strings.TrimSpace(path) == "" {
			return nil, fmt.Errorf("CERT_SIGNER_FILE required for file backend")
		}
		pemBytes, err := os.ReadFile(path)
		if err != nil {
			return nil, err
		}
		block, _ := pem.Decode(pemBytes)
		if block == nil {
			return nil, fmt.Errorf("no PEM block found in %s", path)
		}
		if k, err := x509.ParsePKCS8PrivateKey(block.Bytes); err == nil {
			if priv, ok := k.(ed25519.PrivateKey); ok {
				return &fileSigner{priv: priv}, nil
			}
			return nil, fmt.Errorf("not an Ed25519 private key")
		}
		if len(block.Bytes) == ed25519.PrivateKeySize {
			// A raw Ed25519 private key embeds the public key in its final
			// 32 bytes. Reject mismatches instead of issuing invalid signatures.
			reconstructed := ed25519.NewKeyFromSeed(block.Bytes[:ed25519.SeedSize])
			if subtle.ConstantTimeCompare(reconstructed, block.Bytes) != 1 {
				return nil, fmt.Errorf("inconsistent Ed25519 private key encoding")
			}
			return &fileSigner{priv: reconstructed}, nil
		}
		return nil, fmt.Errorf("unsupported private key format")
	case "kms":
		return nil, fmt.Errorf("kms signing backend is not implemented")
	case "vault":
		return nil, fmt.Errorf("vault signing backend is not implemented")
	default:
		return nil, fmt.Errorf("no signer configured")
	}
}

// CertV1 represents a CERT-V1 certificate
type CertV1 struct {
	BundleID       string                 `json:"bundle_id"`
	PolicyHash     string                 `json:"policy_hash"`
	ProofHash      string                 `json:"proof_hash"`
	AutomataHash   string                 `json:"automata_hash"`
	LabelerHash    string                 `json:"labeler_hash"`
	NIClaim        string                 `json:"ni_claim"`
	NIMonitor      string                 `json:"ni_monitor"` // "inapplicable" | "accept" | "reject" | "error"
	SidecarBuild   string                 `json:"sidecar_build"`
	AttestationRef string                 `json:"attestation_ref,omitempty"`
	Extensions     map[string]interface{} `json:"extensions,omitempty"`
	Timestamp      time.Time              `json:"timestamp"`
	TenantID       string                 `json:"tenant_id"`
	SessionID      string                 `json:"session_id"`
	// Common top-level permission evidence fields
	PermitDecision    string     `json:"permit_decision,omitempty"`
	PathWitnessOK     bool       `json:"path_witness_ok,omitempty"`
	LabelDerivationOK bool       `json:"label_derivation_ok,omitempty"`
	Epoch             int        `json:"epoch,omitempty"`
	EgressProfile     string     `json:"egress_profile,omitempty"`
	Morph             *MorphInfo `json:"morph,omitempty"`
	Sig               string     `json:"sig,omitempty"`
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
	TenantID   string    `json:"tenant_id,omitempty"`
	PolicyHash string    `json:"policy_hash,omitempty"`
	SessionID  string    `json:"session_id,omitempty"`
	StartTime  time.Time `json:"start_time,omitempty"`
	EndTime    time.Time `json:"end_time,omitempty"`
	NIMonitor  string    `json:"ni_monitor,omitempty"`
	Limit      int       `json:"limit,omitempty"`
	Offset     int       `json:"offset,omitempty"`
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

// CertValidationRequest allows server-side validation of raw CERT JSON bytes or structured cert
type CertValidationRequest struct {
	// One of Raw or Cert must be provided
	Raw     json.RawMessage `json:"raw,omitempty"`
	Cert    *CertV1         `json:"cert,omitempty"`
	JWKSURL string          `json:"jwks_url,omitempty"`
	PEMPub  string          `json:"pem_pub,omitempty"` // deprecated: rejected as an untrusted caller key
}

// CertValidationResponse is returned by /evidence/validate
type CertValidationResponse struct {
	SchemaValid      bool              `json:"schema_valid"`
	SignatureChecked bool              `json:"signature_checked"`
	SignatureValid   bool              `json:"signature_valid"`
	Errors           []string          `json:"errors,omitempty"`
	Details          map[string]string `json:"details,omitempty"`
}

// EvidenceService handles CERT-V1 storage, validation, and compliance
type EvidenceService struct {
	db              *sql.DB
	storagePath     string
	schemaData      []byte
	signer          Signer
	trustedJWKSURL  string
	trustedJWKSKeys []ed25519.PublicKey
	access          []evidenceCredential
}

// NewEvidenceService creates a new evidence service instance
func NewEvidenceService() (*EvidenceService, error) {
	access, err := loadEvidenceAccess(os.Getenv("EVIDENCE_ACCESS_FILE"))
	if err != nil {
		return nil, fmt.Errorf("load evidence access configuration: %w", err)
	}
	// An explicitly configured database is a required persistence backend.
	// Filesystem-only development is reserved for installations without a
	// DATABASE_URL setting.
	configuredDBURL := strings.TrimSpace(os.Getenv("DATABASE_URL"))
	var db *sql.DB
	if configuredDBURL != "" {
		var err error
		db, err = sql.Open("postgres", configuredDBURL)
		if err != nil {
			return nil, fmt.Errorf("open configured certificate database: %w", err)
		}
		if err := db.Ping(); err != nil {
			_ = db.Close()
			return nil, fmt.Errorf("configured certificate database unavailable: %w", err)
		}
	}

	// Fetch an operator-pinned JWKS only once, during startup. Inbound
	// validation requests must never supply a network destination or trigger
	// a key download. A configured but unreachable trust root fails startup.
	trustedJWKSURL := strings.TrimSpace(os.Getenv("EVIDENCE_TRUSTED_JWKS_URL"))
	var trustedJWKSKeys []ed25519.PublicKey
	if trustedJWKSURL != "" {
		if err := validateTrustedJWKSURL(trustedJWKSURL); err != nil {
			if db != nil {
				_ = db.Close()
			}
			return nil, fmt.Errorf("invalid configured evidence JWKS endpoint: %w", err)
		}
		keys, err := fetchEd25519KeysFromJWKS(trustedJWKSURL)
		if err != nil {
			if db != nil {
				_ = db.Close()
			}
			return nil, fmt.Errorf("load configured evidence JWKS before serving: %w", err)
		}
		trustedJWKSKeys = keys
	}

	// Storage path
	storagePath := os.Getenv("EVIDENCE_STORAGE_PATH")
	if storagePath == "" {
		storagePath = "/tmp/evidence"
	}
	// Only the filesystem backend needs a local certificate directory.
	if db == nil {
		if err := os.MkdirAll(storagePath, 0755); err != nil {
			return nil, fmt.Errorf("prepare evidence storage directory: %w", err)
		}
	}

	// Load CERT-V1 schema
	schemaPath := "external/CERT-V1/schema/cert-v1.schema.json"
	schemaData, err := os.ReadFile(schemaPath)
	if err != nil {
		log.Printf("Warning: Could not load CERT-V1 schema: %v", err)
		schemaData = []byte(`{"type": "object"}`) // Fallback schema
	}

	service := &EvidenceService{
		db:              db,
		storagePath:     storagePath,
		schemaData:      schemaData,
		trustedJWKSURL:  trustedJWKSURL,
		trustedJWKSKeys: trustedJWKSKeys,
		access:          access,
	}

	// A configured, unusable signer must never silently produce unsigned records.
	if strings.TrimSpace(os.Getenv("CERT_SIGNER_BACKEND")) != "" {
		signer, err := newSignerFromEnv()
		if err != nil {
			if db != nil {
				_ = db.Close()
			}
			return nil, fmt.Errorf("configured certificate signer unavailable: %w", err)
		}
		service.signer = signer
	}

	// Runtime startup only inspects an already migrated schema. It must
	// never perform DDL or connect as a table owner / RLS-bypass role.
	if err := service.validateRuntimeDatabase(); err != nil {
		if db != nil {
			_ = db.Close()
		}
		return nil, fmt.Errorf("validate certificate runtime database: %w", err)
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
	
	-- PostgreSQL does not implement CREATE POLICY IF NOT EXISTS.
	-- Replace only this service-owned policy within a single transaction,
	-- preventing stale or overly permissive definitions from being reused.
	DROP POLICY IF EXISTS tenant_isolation ON certificates;
	CREATE POLICY tenant_isolation ON certificates
		FOR ALL TO PUBLIC
		USING (tenant_id = current_setting('app.current_tenant', true))
		WITH CHECK (tenant_id = current_setting('app.current_tenant', true));
	`

	tx, err := s.db.BeginTx(context.Background(), nil)
	if err != nil {
		return fmt.Errorf("start certificate schema transaction: %w", err)
	}
	defer tx.Rollback()
	if _, err := tx.Exec(schema); err != nil {
		return fmt.Errorf("apply certificate schema and RLS policy: %w", err)
	}
	if err := tx.Commit(); err != nil {
		return fmt.Errorf("commit certificate schema and RLS policy: %w", err)
	}
	return nil
}

// StoreCertificate validates and stores a CERT-V1 certificate
func (s *EvidenceService) StoreCertificate(ctx context.Context, cert CertV1) error {
	// Validate certificate against CERT-V1 schema
	if err := s.validateCertificate(cert); err != nil {
		return fmt.Errorf("certificate validation failed: %w", err)
	}

	// Prepare one canonical, signed certificate before either persistence
	// backend is accessed. Signing failures must leave no partial record.
	prepared, err := s.prepareCertificate(cert)
	if err != nil {
		return fmt.Errorf("certificate preparation failed: %w", err)
	}

	// Select exactly one authoritative backend. A second write after a
	// successful database commit would report failure despite a durable row.
	// Filesystem mode is explicit; it is neither a mirror nor a fallback.
	if s.db != nil {
		if err := s.storeCertInDB(ctx, prepared); err != nil {
			return fmt.Errorf("database certificate storage failed: %w", err)
		}
		return nil
	}

	if err := s.writeCertInFS(prepared); err != nil {
		return fmt.Errorf("filesystem storage failed: %w", err)
	}

	return nil
}

// validateSearchPagination rejects invalid external and internal search parameters.
func validateSearchPagination(req CertSearchRequest) error {
	if req.Limit < 0 || req.Offset < 0 {
		return fmt.Errorf("limit and offset must be nonnegative")
	}
	return nil
}

// SearchCertificates searches for certificates based on criteria
func (s *EvidenceService) SearchCertificates(ctx context.Context, req CertSearchRequest) (*CertSearchResponse, error) {
	if err := validateSearchPagination(req); err != nil {
		return nil, err
	}
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
		certs, count, err := s.searchCertsInDB(ctx, req)
		if err != nil {
			return nil, fmt.Errorf("database certificate search failed: %w", err)
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
	if err := validateEvidencePathSegment("tenant_id", cert.TenantID); err != nil {
		return err
	}
	if err := validateEvidencePathSegment("session_id", cert.SessionID); err != nil {
		return err
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
func (s *EvidenceService) storeCertInDB(ctx context.Context, cert CertV1) error {
	tx, err := s.beginTenantTx(ctx, cert.TenantID, false)
	if err != nil {
		return err
	}
	defer tx.Rollback()
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

	_, err = tx.ExecContext(ctx, query,
		cert.BundleID, cert.PolicyHash, cert.ProofHash, cert.AutomataHash,
		cert.LabelerHash, cert.NIClaim, cert.NIMonitor, cert.SidecarBuild,
		cert.TenantID, cert.SessionID, cert.Timestamp, string(certData),
	)

	if err != nil {
		return err
	}
	return tx.Commit()
}

// prepareCertificate normalizes the stored fields and signs those exact bytes.
// It does not establish the truth of the caller-provided evidence claims.
func (s *EvidenceService) prepareCertificate(cert CertV1) (CertV1, error) {
	if s.signer == nil && cert.Sig != "" {
		return CertV1{}, fmt.Errorf("pre-signed certificates require separate trusted verification")
	}
	// Avoid mutating the caller's map when populating permission evidence.
	extensions := make(map[string]interface{}, len(cert.Extensions)+5)
	for key, value := range cert.Extensions {
		extensions[key] = value
	}
	cert.Extensions = extensions
	if cert.PermitDecision != "" {
		cert.Extensions["permit_decision"] = cert.PermitDecision
	}
	cert.Extensions["path_witness_ok"] = cert.PathWitnessOK
	cert.Extensions["label_derivation_ok"] = cert.LabelDerivationOK
	if cert.Epoch != 0 {
		cert.Extensions["permission_epoch"] = cert.Epoch
	}
	if cert.EgressProfile != "" {
		cert.Extensions["egress_profile"] = cert.EgressProfile
	}

	if s.signer != nil {
		// Never incorporate a caller-supplied signature into a new issuance.
		cert.Sig = ""
		encoded, err := json.Marshal(cert)
		if err != nil {
			return CertV1{}, fmt.Errorf("encode certificate for signing: %w", err)
		}
		claims, err := decodeEvidenceObject(encoded)
		if err != nil {
			return CertV1{}, fmt.Errorf("decode certificate for signing: %w", err)
		}
		canonical, err := marshalCanonicalJSON(claims)
		if err != nil {
			return CertV1{}, fmt.Errorf("canonicalize certificate: %w", err)
		}
		signature, err := s.signer.Sign(canonical)
		if err != nil {
			return CertV1{}, fmt.Errorf("sign certificate: %w", err)
		}
		signatureBytes, err := base64.RawURLEncoding.DecodeString(signature)
		if err != nil || len(signatureBytes) != ed25519.SignatureSize {
			return CertV1{}, fmt.Errorf("signer returned invalid Ed25519 signature encoding")
		}
		cert.Sig = signature
	}
	return cert, nil
}

// storeCertInFS preserves the internal direct-call contract for storage tests.
func (s *EvidenceService) storeCertInFS(cert CertV1) error {
	prepared, err := s.prepareCertificate(cert)
	if err != nil {
		return err
	}
	return s.writeCertInFS(prepared)
}

// writeCertInFS persists an already prepared certificate.
func (s *EvidenceService) writeCertInFS(cert CertV1) error {
	// Validate again at the storage boundary for callers that bypass
	// StoreCertificate. os.Root confines traversal through existing symlinks.
	if err := validateEvidencePathSegment("tenant_id", cert.TenantID); err != nil {
		return err
	}
	if err := validateEvidencePathSegment("session_id", cert.SessionID); err != nil {
		return err
	}
	if err := os.MkdirAll(s.storagePath, 0755); err != nil {
		return fmt.Errorf("prepare evidence storage: %w", err)
	}
	root, err := os.OpenRoot(s.storagePath)
	if err != nil {
		return fmt.Errorf("open evidence storage root: %w", err)
	}
	defer root.Close()

	certDir := filepath.Join("certs", cert.TenantID, cert.SessionID)
	if err := root.MkdirAll(certDir, 0755); err != nil {
		return fmt.Errorf("prepare certificate directory: %w", err)
	}

	// Create a new certificate file inside the confined storage root.
	filename := fmt.Sprintf("%d_%s.cert.json", cert.Timestamp.Unix(), uuid.New().String()[:8])
	certPath := filepath.Join(certDir, filename)

	// Write certificate
	certData, err := json.MarshalIndent(cert, "", "  ")
	if err != nil {
		return err
	}

	file, err := root.OpenFile(certPath, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0644)
	if err != nil {
		return fmt.Errorf("create certificate file: %w", err)
	}
	if _, err := file.Write(certData); err != nil {
		_ = file.Close()
		_ = root.Remove(certPath)
		return fmt.Errorf("write certificate file: %w", err)
	}
	if err := file.Close(); err != nil {
		_ = root.Remove(certPath)
		return fmt.Errorf("close certificate file: %w", err)
	}
	return nil
}

// searchCertsInDB searches certificates in database
func (s *EvidenceService) searchCertsInDB(ctx context.Context, req CertSearchRequest) ([]CertV1, int, error) {
	tx, err := s.beginTenantTx(ctx, req.TenantID, true)
	if err != nil {
		return nil, 0, err
	}
	defer tx.Rollback()
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
	err = tx.QueryRowContext(ctx, countQuery, args...).Scan(&total)
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

	rows, err := tx.QueryContext(ctx, dataQuery, args...)
	if err != nil {
		return nil, 0, err
	}
	defer rows.Close()

	var certificates []CertV1
	for rows.Next() {
		var certData string
		if err := rows.Scan(&certData); err != nil {
			return nil, 0, fmt.Errorf("scan certificate row: %w", err)
		}

		var cert CertV1
		if err := json.Unmarshal([]byte(certData), &cert); err != nil {
			return nil, 0, fmt.Errorf("decode stored certificate row: %w", err)
		}

		if req.TenantID != "" && cert.TenantID != req.TenantID {
			return nil, 0, fmt.Errorf("stored certificate tenant does not match query scope")
		}
		certificates = append(certificates, cert)
	}
	if err := rows.Err(); err != nil {
		return nil, 0, fmt.Errorf("iterate certificate rows: %w", err)
	}

	if err := rows.Close(); err != nil {
		return nil, 0, err
	}
	if err := tx.Commit(); err != nil {
		return nil, 0, err
	}
	return certificates, total, nil
}

// searchCertsInFS searches certificates in filesystem (fallback)
func (s *EvidenceService) searchCertsInFS(req CertSearchRequest) (*CertSearchResponse, error) {
	var certificates []CertV1

	certsDir := filepath.Join(s.storagePath, "certs")
	// A new, empty evidence store has no certificate directory.
	dirInfo, err := os.Lstat(certsDir)
	if os.IsNotExist(err) {
		return &CertSearchResponse{Certificates: []CertV1{}, Total: 0, Limit: req.Limit, Offset: req.Offset}, nil
	}
	if err != nil {
		return nil, fmt.Errorf("inspect certificate directory: %w", err)
	}
	if !dirInfo.IsDir() {
		return nil, fmt.Errorf("certificate directory is not a directory")
	}
	root, err := os.OpenRoot(s.storagePath)
	if err != nil {
		return nil, fmt.Errorf("open certificate storage root: %w", err)
	}
	defer root.Close()

	err = filepath.Walk(certsDir, func(path string, info os.FileInfo, walkErr error) error {
		if walkErr != nil {
			return fmt.Errorf("walk certificate storage: %w", walkErr)
		}
		if info.Mode()&os.ModeSymlink != 0 {
			return fmt.Errorf("symlink in certificate storage")
		}
		if !strings.HasSuffix(info.Name(), ".cert.json") {
			return nil
		}
		if !info.Mode().IsRegular() {
			return fmt.Errorf("certificate is not a regular file")
		}

		relative, err := filepath.Rel(s.storagePath, path)
		if err != nil {
			return fmt.Errorf("resolve certificate path: %w", err)
		}
		// Use the confined root even if a path is replaced after Walk
		// inspects it; symlinks cannot escape the storage root.
		file, err := root.Open(relative)
		if err != nil {
			return fmt.Errorf("open confined certificate: %w", err)
		}
		data, readErr := io.ReadAll(file)
		closeErr := file.Close()
		if readErr != nil {
			return fmt.Errorf("read certificate: %w", readErr)
		}
		if closeErr != nil {
			return fmt.Errorf("close certificate: %w", closeErr)
		}
		var cert CertV1
		if err := json.Unmarshal(data, &cert); err != nil {
			return fmt.Errorf("decode filesystem certificate: %w", err)
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
	if start > total {
		start = total
	}
	// Clamp before adding so a huge caller offset cannot wrap the integer.
	end := start + req.Limit
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
		certData, err := json.Marshal(cert)
		if err != nil {
			return "", fmt.Errorf("encode certificate for diagnostic digest: %w", err)
		}
		hash := fmt.Sprintf("%x", sha256.Sum256(certData))
		hashes = append(hashes, hash)
	}

	// Create audit proof structure
	auditProof := map[string]interface{}{
		"certificate_count": len(certs),
		"hash_chain":        hashes,
		"root_hash":         s.calculateRootHash(hashes),
		"generated_at":      time.Now().Unix(),
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

	report.WriteString("# Certificate Claims Summary\n\n")
	report.WriteString("This diagnostic summarizes stored assertions; it does not establish independent proof validity or compliance.\n\n")
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
		// Identifiers are currently only validated as nonempty strings.
		report.WriteString(fmt.Sprintf("- Policy %q: %d certificates\n", hash, count))
	}

	// Compliance summary
	report.WriteString("\n## Recorded Monitor Outcomes\n\n")
	acceptCount := niMonitorCounts["accept"]
	totalCount := len(certs)

	if totalCount > 0 {
		complianceRate := float64(acceptCount) / float64(totalCount) * 100
		report.WriteString(fmt.Sprintf("- Recorded accept rate: %.2f%%\n", complianceRate))
		report.WriteString(fmt.Sprintf("- Total Decisions: %d\n", totalCount))
		report.WriteString(fmt.Sprintf("- Accepted: %d\n", acceptCount))
		report.WriteString(fmt.Sprintf("- Rejected: %d\n", niMonitorCounts["reject"]))
		report.WriteString(fmt.Sprintf("- Errors: %d\n", niMonitorCounts["error"]))
		report.WriteString(fmt.Sprintf("- Inapplicable: %d\n", niMonitorCounts["inapplicable"]))
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
func writeError(c *gin.Context, status int, code, cause, action, docs string) {
	c.JSON(status, gin.H{
		"error": gin.H{
			"code":     code,
			"cause":    cause,
			"action":   action,
			"docs_url": docs,
		},
	})
}

func (s *EvidenceService) storeCertHandler(c *gin.Context) {
	var cert CertV1
	if err := c.ShouldBindJSON(&cert); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_REQUEST", err.Error(), "Fix JSON payload and retry", "https://docs.sentinelops.dev/error-catalog#INVALID_REQUEST")
		return
	}

	if err := s.validateCertificate(cert); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_CERTIFICATE", err.Error(), "Correct certificate fields and retry", "https://docs.sentinelops.dev/error-catalog#INVALID_CERTIFICATE")
		return
	}
	if _, ok := s.authorizeEvidence(c, cert.TenantID, true); !ok {
		return
	}
	// Authenticated storage access is not independent proof verification.
	if s.signer != nil {
		writeError(c, http.StatusServiceUnavailable, "EVIDENCE_ISSUANCE_UNAVAILABLE",
			"Authenticated evidence provenance verification is not implemented",
			"Use a separately qualified issuance path", "")
		return
	}
	if err := s.StoreCertificate(c.Request.Context(), cert); err != nil {
		writeError(c, http.StatusInternalServerError, "CERT_STORE_FAILED", err.Error(), "Check storage and retry", "https://docs.sentinelops.dev/error-catalog#CERT_STORE_FAILED")
		return
	}

	c.JSON(http.StatusCreated, gin.H{"status": "stored"})
}

func (s *EvidenceService) searchCertsHandler(c *gin.Context) {
	var req CertSearchRequest
	if err := c.ShouldBindJSON(&req); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_REQUEST", err.Error(), "Fix JSON payload and retry", "https://docs.sentinelops.dev/error-catalog#INVALID_REQUEST")
		return
	}

	if err := validateSearchPagination(req); err != nil {
		writeError(c, http.StatusBadRequest, "INVALID_REQUEST", err.Error(), "Use nonnegative limit and offset values", "https://docs.sentinelops.dev/error-catalog#INVALID_REQUEST")
		return
	}
	tenant, ok := s.authorizeEvidence(c, req.TenantID, false)
	if !ok {
		return
	}
	req.TenantID = tenant
	resp, err := s.SearchCertificates(c.Request.Context(), req)
	if err != nil {
		writeError(c, http.StatusInternalServerError, "CERT_SEARCH_FAILED", err.Error(), "Retry later or narrow filters", "https://docs.sentinelops.dev/error-catalog#CERT_SEARCH_FAILED")
		return
	}

	c.JSON(http.StatusOK, resp)
}

func (s *EvidenceService) getCertHandler(c *gin.Context) {
	certID := c.Param("id")

	tenant, ok := s.authorizeEvidence(c, "", false)
	if !ok {
		return
	}
	// Search by ID within the authenticated tenant.
	req := CertSearchRequest{
		TenantID:  tenant,
		SessionID: certID,
		Limit:     1,
	}

	resp, err := s.SearchCertificates(c.Request.Context(), req)
	if err != nil {
		writeError(c, http.StatusInternalServerError, "CERT_SEARCH_FAILED", err.Error(), "Retry later or narrow filters", "https://docs.sentinelops.dev/error-catalog#CERT_SEARCH_FAILED")
		return
	}

	if len(resp.Certificates) == 0 {
		writeError(c, http.StatusNotFound, "CERT_NOT_FOUND", "Certificate not found", "Check session id or time window", "https://docs.sentinelops.dev/error-catalog#CERT_NOT_FOUND")
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

	tenant, ok := s.authorizeEvidence(c, req.TenantID, false)
	if !ok {
		return
	}
	req.TenantID = tenant
	packet, err := s.BuildCompliancePacket(c.Request.Context(), req)
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
		return
	}

	c.JSON(http.StatusOK, packet)
}

// downloadPacketHandler intentionally refuses a compliance archive. The JSON
// packet returned by POST is not persisted, so an arbitrary packet ID cannot
// identify authentic evidence. No archive is synthesized from that ID.
func (_ *EvidenceService) downloadPacketHandler(c *gin.Context) {
	writeError(
		c,
		http.StatusNotImplemented,
		"PACKET_EXPORT_UNAVAILABLE",
		"Compliance packet archives are unavailable: no authenticated, persisted packet corresponds to the requested ID",
		"Use POST /api/v1/compliance/packet for an in-request JSON diagnostic only; it is not a certified evidence archive",
		"",
	)
}

func (s *EvidenceService) healthHandler(c *gin.Context) {
	dbStatus := "disconnected"
	storageBackend := "filesystem"
	if s.db != nil {
		storageBackend = "postgres"
		if err := s.db.Ping(); err == nil {
			dbStatus = "connected"
		}
	}

	c.JSON(http.StatusOK, gin.H{
		"status":          "healthy",
		"service":         "evidence-service",
		"version":         "1.0.0",
		"timestamp":       time.Now(),
		"database":        dbStatus,
		"storage":         s.storagePath,
		"storage_backend": storageBackend,
	})
}

func (s *EvidenceService) verifyCertHandler(c *gin.Context) {
	// Retain original bytes for both supported request forms. Decoding into
	// CertV1 here would discard unknown fields and round extension numbers.
	body, err := io.ReadAll(http.MaxBytesReader(c.Writer, c.Request.Body, maxEvidenceJSONBytes))
	if err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": "invalid or oversized validation request"})
		return
	}
	request, err := decodeEvidenceObject(body)
	if err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": "ambiguous or unsupported validation JSON"})
		return
	}
	// Exact field names avoid encoding/json's case-insensitive struct
	// field matching at the request trust boundary.
	for key := range request {
		switch key {
		case "raw", "cert", "jwks_url", "pem_pub":
		default:
			c.JSON(http.StatusBadRequest, gin.H{"error": "unknown validation request field"})
			return
		}
	}
	var pemPub, jwksURL string
	if value, present := request["pem_pub"]; present {
		var ok bool
		pemPub, ok = value.(string)
		if !ok {
			c.JSON(http.StatusBadRequest, gin.H{"error": "invalid verifier key field"})
			return
		}
	}
	if value, present := request["jwks_url"]; present {
		var ok bool
		jwksURL, ok = value.(string)
		if !ok {
			c.JSON(http.StatusBadRequest, gin.H{"error": "invalid JWKS field"})
			return
		}
	}
	// An attacker could sign arbitrary claims with their own key and submit
	// that key as pem_pub. Signature-valid means trusted issuer verification,
	// never just self-consistency under a request-provided public key.
	if strings.TrimSpace(pemPub) != "" {
		writeError(c, http.StatusBadRequest, "UNTRUSTED_VERIFIER_KEY",
			"Caller-supplied verification keys are not accepted",
			"Configure an operator-controlled trusted JWKS before validating signatures", "")
		return
	}
	// Callers cannot make the evidence service fetch arbitrary origins. A
	// request JWKS URL is usable only if the deployment explicitly pinned it.
	if err := s.approveJWKSURL(jwksURL); err != nil {
		c.JSON(http.StatusBadRequest, gin.H{"error": "unapproved JWKS endpoint"})
		return
	}

	payload, rawPresent := request["raw"]
	structured, certPresent := request["cert"]
	if rawPresent == certPresent {
		c.JSON(http.StatusBadRequest, gin.H{"error": "provide exactly one certificate payload"})
		return
	}
	if certPresent {
		payload = structured
	}
	generic, ok := payload.(map[string]interface{})
	if !ok {
		c.JSON(http.StatusBadRequest, gin.H{"error": "certificate payload must be an object"})
		return
	}

	resp := CertValidationResponse{Details: map[string]string{}}

	// Schema validation (quick structural check; can be replaced with full jsonschema)
	if err := s.quickSchemaValidate(generic); err != nil {
		resp.SchemaValid = false
		resp.Errors = append(resp.Errors, err.Error())
	} else {
		resp.SchemaValid = true
	}

	// Signature validation (optional if sig present)
	sigVal, hasSig := generic["sig"]
	if hasSig {
		resp.SignatureChecked = true
		delete(generic, "sig")
		canon, err := marshalCanonicalJSON(generic)
		if err != nil {
			resp.Errors = append(resp.Errors, "canonicalize_error")
			c.JSON(http.StatusOK, resp)
			return
		}
		sigStr, _ := sigVal.(string)
		valid, reason := verifySignature(canon, sigStr, s.trustedJWKSKeys)
		resp.SignatureValid = valid
		if !valid {
			resp.Errors = append(resp.Errors, reason)
		}
	} else {
		resp.SignatureChecked = false
	}

	c.JSON(http.StatusOK, resp)
}

func (s *EvidenceService) quickSchemaValidate(cert map[string]interface{}) error {
	required := []string{"bundle_id", "policy_hash", "proof_hash", "automata_hash", "labeler_hash", "ni_monitor", "permit_decision", "path_witness_ok", "label_derivation_ok", "epoch", "egress_profile"}
	for _, k := range required {
		if _, ok := cert[k]; !ok {
			return fmt.Errorf("missing required field: %s", k)
		}
	}
	if v, ok := cert["ni_monitor"].(string); ok {
		switch v {
		case "inapplicable", "accept", "reject", "error":
		default:
			return fmt.Errorf("invalid ni_monitor value: %s", v)
		}
	} else {
		return fmt.Errorf("ni_monitor must be string")
	}
	return nil
}

func verifySignature(message []byte, sigBase64 string, trustedKeys []ed25519.PublicKey) (bool, string) {
	// decode base64 (std or url)
	var sig []byte
	if b, err := base64.StdEncoding.DecodeString(sigBase64); err == nil {
		sig = b
	} else if b2, err2 := base64.RawURLEncoding.DecodeString(sigBase64); err2 == nil {
		sig = b2
	} else {
		return false, "sig_decode_error"
	}
	if len(trustedKeys) == 0 {
		return false, "trusted_verifier_unavailable"
	}
	// These keys were loaded from a deployment-controlled URL at startup.
	// No input supplied by a validation caller can trigger a network fetch.
	for _, pub := range trustedKeys {
		if ed25519.Verify(pub, message, sig) {
			return true, ""
		}
	}
	return false, "signature_mismatch"
}

func loadEd25519PublicKeyFromPEMString(pemData string) (ed25519.PublicKey, error) {
	block, _ := pem.Decode([]byte(pemData))
	if block == nil {
		return nil, fmt.Errorf("no PEM block found")
	}
	// Try PKIX
	if pub, err := x509.ParsePKIXPublicKey(block.Bytes); err == nil {
		if ed, ok := pub.(ed25519.PublicKey); ok {
			return ed, nil
		}
		return nil, fmt.Errorf("not an Ed25519 public key")
	}
	// Try raw bytes
	if len(block.Bytes) == ed25519.PublicKeySize {
		return ed25519.PublicKey(block.Bytes), nil
	}
	return nil, fmt.Errorf("unsupported public key format")
}

// marshalCanonicalJSON encodes a value with deterministic key ordering (RFC-like)
func marshalCanonicalJSON(v interface{}) ([]byte, error) {
	var buf bytes.Buffer
	if err := writeCanonicalJSON(&buf, v); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func writeCanonicalJSON(buf *bytes.Buffer, v interface{}) error {
	switch t := v.(type) {
	case map[string]interface{}:
		buf.WriteByte('{')
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for i, k := range keys {
			kb, _ := json.Marshal(k)
			buf.Write(kb)
			buf.WriteByte(':')
			if err := writeCanonicalJSON(buf, t[k]); err != nil {
				return err
			}
			if i < len(keys)-1 {
				buf.WriteByte(',')
			}
		}
		buf.WriteByte('}')
		return nil
	case []interface{}:
		buf.WriteByte('[')
		for i, elem := range t {
			if err := writeCanonicalJSON(buf, elem); err != nil {
				return err
			}
			if i < len(t)-1 {
				buf.WriteByte(',')
			}
		}
		buf.WriteByte(']')
		return nil
	case json.Number:
		b, err := canonicalEvidenceNumber(t)
		if err != nil {
			return err
		}
		buf.Write(b)
		return nil
	case string, float64, float32, bool, int, int64, nil:
		b, err := json.Marshal(t)
		if err != nil {
			return err
		}
		buf.Write(b)
		return nil
	default:
		b, err := json.Marshal(t)
		if err != nil {
			return err
		}
		vv, err := decodeEvidenceValue(b)
		if err != nil {
			return err
		}
		return writeCanonicalJSON(buf, vv)
	}
}

// fetchEd25519KeysFromJWKS fetches public keys; kept minimal to avoid extra deps
// validateTrustedJWKSURL rejects implicit schemes, plaintext endpoints,
// userinfo, and fragments. Only administrators control the approved endpoint.
func validateTrustedJWKSURL(endpoint string) error {
	u, err := neturl.Parse(endpoint)
	if err != nil || u.Scheme != "https" || u.Hostname() == "" ||
		u.User != nil || u.Fragment != "" || u.Opaque != "" {
		return fmt.Errorf("JWKS endpoint must be an absolute HTTPS URL without credentials or fragments")
	}
	return nil
}

// approveJWKSURL establishes an exact deployment-controlled origin binding.
// An absent requested URL keeps local PEM-key diagnostics network-free.
func (s *EvidenceService) approveJWKSURL(requested string) error {
	if requested == "" {
		return nil
	}
	if s.trustedJWKSURL == "" || requested != s.trustedJWKSURL {
		return fmt.Errorf("JWKS endpoint is not configured or does not match the trusted endpoint")
	}
	return nil
}

func fetchEd25519KeysFromJWKS(endpoint string) ([]ed25519.PublicKey, error) {
	if err := validateTrustedJWKSURL(endpoint); err != nil {
		return nil, err
	}
	client := &http.Client{
		Timeout: 5 * time.Second,
		// Never follow an HTTP redirect to a different origin or private
		// address. The operator must pin the final URL explicitly.
		CheckRedirect: func(_ *http.Request, _ []*http.Request) error {
			return http.ErrUseLastResponse
		},
	}
	return fetchEd25519KeysFromJWKSWithClient(client, endpoint)
}

// The client parameter permits real TLS/redirect/size controls in tests.
// Production callers only reach this via the bounded hardened client above.
func fetchEd25519KeysFromJWKSWithClient(client *http.Client, endpoint string) ([]ed25519.PublicKey, error) {
	resp, err := client.Get(endpoint)
	if err != nil {
		return nil, fmt.Errorf("retrieve trusted JWKS: %w", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("JWKS returned HTTP %s", resp.Status)
	}
	var jwks struct {
		Keys []struct {
			Kty string `json:"kty"`
			Crv string `json:"crv"`
			X   string `json:"x"`
			Use string `json:"use"`
			Alg string `json:"alg"`
			Kid string `json:"kid"`
		} `json:"keys"`
	}
	const maxJWKSBytes = 1 << 20
	data, err := io.ReadAll(io.LimitReader(resp.Body, maxJWKSBytes+1))
	if err != nil {
		return nil, fmt.Errorf("read trusted JWKS: %w", err)
	}
	if len(data) > maxJWKSBytes {
		return nil, fmt.Errorf("trusted JWKS exceeds 1 MiB")
	}
	if err := json.Unmarshal(data, &jwks); err != nil {
		return nil, fmt.Errorf("decode trusted JWKS: %w", err)
	}
	var pubs []ed25519.PublicKey
	for _, k := range jwks.Keys {
		if strings.EqualFold(k.Kty, "OKP") && strings.EqualFold(k.Crv, "Ed25519") {
			if raw, err := base64.RawURLEncoding.DecodeString(k.X); err == nil {
				if len(raw) == ed25519.PublicKeySize {
					pubs = append(pubs, ed25519.PublicKey(raw))
				}
			}
		}
	}
	if len(pubs) == 0 {
		return nil, fmt.Errorf("no ed25519 keys in JWKS")
	}
	return pubs, nil
}

func main() {
	if len(os.Args) == 2 && os.Args[1] == "--migrate" {
		if err := migrateEvidenceDatabase(); err != nil {
			log.Fatalf("Evidence database migration failed: %v", err)
		}
		log.Print("Evidence database migration completed")
		return
	}
	if len(os.Args) != 1 {
		log.Fatal("usage: evidence-service [--migrate]")
	}
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
		// The console submits certificate payloads with POST. Keep the legacy
		// GET-with-body route temporarily for existing callers.
		v1.POST("/evidence/validate", service.verifyCertHandler)
		v1.GET("/evidence/validate", service.verifyCertHandler)
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
