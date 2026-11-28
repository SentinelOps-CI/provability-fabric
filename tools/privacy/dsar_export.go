// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"archive/zip"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"time"

	"github.com/spf13/cobra"
	"golang.org/x/crypto/openpgp"
	"golang.org/x/crypto/openpgp/armor"
	"golang.org/x/crypto/openpgp/packet"
)

// DSARData represents the structure of exported data
type DSARData struct {
	TenantID    string                 `json:"tenant_id"`
	ExportDate  time.Time              `json:"export_date"`
	UsageEvents []UsageEvent           `json:"usage_events,omitempty"`
	Capsules    []Capsule              `json:"capsules,omitempty"`
	Metadata    map[string]interface{} `json:"metadata"`
}

// UsageEvent represents usage data with PII redacted
type UsageEvent struct {
	ID        string    `json:"id"`
	TenantID  string    `json:"tenant_id"`
	CPUMs     int64     `json:"cpu_ms"`
	NetBytes  int64     `json:"net_bytes"`
	Timestamp time.Time `json:"timestamp"`
	// Note: No PII fields like email, IP addresses, etc.
}

// Capsule represents capsule data with PII redacted
type Capsule struct {
	ID        string    `json:"id"`
	Hash      string    `json:"hash"`
	SpecSig   string    `json:"spec_sig"`
	RiskScore float64   `json:"risk_score"`
	Reason    *string   `json:"reason,omitempty"`
	TenantID  string    `json:"tenant_id"`
	CreatedAt time.Time `json:"created_at"`
	UpdatedAt time.Time `json:"updated_at"`
	// Note: No PII fields like user names, emails, etc.
}

// DSARExporter handles the export process
type DSARExporter struct {
	ledgerURL     string
	tenantID      string
	afterDate     time.Time
	outputPath    string
	publicKeyPath string
}

func main() {
	var rootCmd = &cobra.Command{
		Use:   "dsar-export",
		Short: "Export DSAR (Data Subject Access Request) data for a tenant",
		Long: `Export DSAR data for a tenant with PII redaction and encryption.
		
This tool exports UsageEvent and Capsule data for a tenant, redacts all PII,
and creates an encrypted ZIP file that can be securely transmitted to the data subject.`,
	}

	var (
		ledgerURL     string
		tenantID      string
		afterDate     string
		outputPath    string
		publicKeyPath string
	)

	rootCmd.Flags().StringVar(&ledgerURL, "ledger-url", "http://localhost:3000", "Ledger service URL")
	rootCmd.Flags().StringVar(&tenantID, "tenant", "", "Tenant ID to export data for")
	rootCmd.Flags().StringVar(&afterDate, "after", "", "Export data after this date (YYYY-MM-DD)")
	rootCmd.Flags().StringVar(&outputPath, "output", "", "Output ZIP file path")
	rootCmd.Flags().StringVar(&publicKeyPath, "public-key", "", "Path to recipient's public key for encryption")

	rootCmd.MarkFlagRequired("tenant")
	rootCmd.MarkFlagRequired("output")
	rootCmd.MarkFlagRequired("public-key")

	rootCmd.RunE = func(cmd *cobra.Command, args []string) error {
		// Parse after date
		var after time.Time
		if afterDate != "" {
			var err error
			after, err = time.Parse("2006-01-02", afterDate)
			if err != nil {
				return fmt.Errorf("invalid date format: %v", err)
			}
		}

		exporter := &DSARExporter{
			ledgerURL:     ledgerURL,
			tenantID:      tenantID,
			afterDate:     after,
			outputPath:    outputPath,
			publicKeyPath: publicKeyPath,
		}

		return exporter.Export()
	}

	if err := rootCmd.Execute(); err != nil {
		log.Fatal(err)
	}
}

// Export performs the DSAR export process
func (e *DSARExporter) Export() error {
	log.Printf("Starting DSAR export for tenant: %s", e.tenantID)

	// 1. Gather usage events
	usageEvents, err := e.gatherUsageEvents()
	if err != nil {
		return fmt.Errorf("failed to gather usage events: %v", err)
	}
	log.Printf("Gathered %d usage events", len(usageEvents))

	// 2. Gather capsules
	capsules, err := e.gatherCapsules()
	if err != nil {
		return fmt.Errorf("failed to gather capsules: %v", err)
	}
	log.Printf("Gathered %d capsules", len(capsules))

	// 3. Create DSAR data structure
	dsarData := DSARData{
		TenantID:    e.tenantID,
		ExportDate:  time.Now().UTC(),
		UsageEvents: usageEvents,
		Capsules:    capsules,
		Metadata: map[string]interface{}{
			"export_version": "1.0",
			"pii_redacted":   true,
			"encrypted":      true,
			"after_date":     e.afterDate,
		},
	}

	// 4. Create encrypted ZIP
	if err := e.createEncryptedZip(dsarData); err != nil {
		return fmt.Errorf("failed to create encrypted ZIP: %v", err)
	}

	log.Printf("DSAR export completed: %s", e.outputPath)
	return nil
}

// gatherUsageEvents retrieves and redacts usage events
func (e *DSARExporter) gatherUsageEvents() ([]UsageEvent, error) {
	// In a real implementation, this would query the ledger service
	// For now, we'll create mock data to demonstrate the structure

	mockEvents := []UsageEvent{
		{
			ID:        "event-1",
			TenantID:  e.tenantID,
			CPUMs:     1500,
			NetBytes:  1024000,
			Timestamp: time.Now().Add(-24 * time.Hour),
		},
		{
			ID:        "event-2",
			TenantID:  e.tenantID,
			CPUMs:     2300,
			NetBytes:  2048000,
			Timestamp: time.Now().Add(-12 * time.Hour),
		},
	}

	// Filter by date if specified
	if !e.afterDate.IsZero() {
		filtered := make([]UsageEvent, 0)
		for _, event := range mockEvents {
			if event.Timestamp.After(e.afterDate) {
				filtered = append(filtered, event)
			}
		}
		return filtered, nil
	}

	return mockEvents, nil
}

// gatherCapsules retrieves and redacts capsule data
func (e *DSARExporter) gatherCapsules() ([]Capsule, error) {
	// In a real implementation, this would query the ledger service
	// For now, we'll create mock data to demonstrate the structure

	mockCapsules := []Capsule{
		{
			ID:        "capsule-1",
			Hash:      "sha256:abc123...",
			SpecSig:   "sig:def456...",
			RiskScore: 0.15,
			Reason:    nil,
			TenantID:  e.tenantID,
			CreatedAt: time.Now().Add(-48 * time.Hour),
			UpdatedAt: time.Now().Add(-24 * time.Hour),
		},
		{
			ID:        "capsule-2",
			Hash:      "sha256:ghi789...",
			SpecSig:   "sig:jkl012...",
			RiskScore: 0.85,
			Reason:    stringPtr("High risk activity detected"),
			TenantID:  e.tenantID,
			CreatedAt: time.Now().Add(-12 * time.Hour),
			UpdatedAt: time.Now().Add(-6 * time.Hour),
		},
	}

	// Filter by date if specified
	if !e.afterDate.IsZero() {
		filtered := make([]Capsule, 0)
		for _, capsule := range mockCapsules {
			if capsule.CreatedAt.After(e.afterDate) {
				filtered = append(filtered, capsule)
			}
		}
		return filtered, nil
	}

	return mockCapsules, nil
}

// createEncryptedZip finalizes a temporary ZIP before encrypting and publishing it.
// The plaintext archive stays in a private, short-lived file in the output directory.
// An error never publishes an incomplete ZIP or exposes plaintext at the output path.
func (e *DSARExporter) createEncryptedZip(data DSARData) error {
	jsonData, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal DSAR data: %w", err)
	}

	archive, err := os.CreateTemp(filepath.Dir(e.outputPath), ".dsar-export-*")
	if err != nil {
		return fmt.Errorf("failed to create temporary DSAR archive: %w", err)
	}
	archivePath := archive.Name()
	defer os.Remove(archivePath)

	writer := zip.NewWriter(archive)
	entry, err := writer.Create("dsar-data.json")
	if err != nil {
		_ = writer.Close()
		_ = archive.Close()
		return fmt.Errorf("failed to create ZIP entry: %w", err)
	}
	if _, err := entry.Write(jsonData); err != nil {
		_ = writer.Close()
		_ = archive.Close()
		return fmt.Errorf("failed to write DSAR data: %w", err)
	}
	// ZIP's central directory is emitted by Close, not by Write.
	if err := writer.Close(); err != nil {
		_ = archive.Close()
		return fmt.Errorf("failed to finalize DSAR ZIP: %w", err)
	}
	if err := archive.Close(); err != nil {
		return fmt.Errorf("failed to close DSAR ZIP: %w", err)
	}

	if err := e.encryptFile(archivePath); err != nil {
		return fmt.Errorf("failed to encrypt DSAR ZIP: %w", err)
	}
	if err := os.Rename(archivePath, e.outputPath); err != nil {
		return fmt.Errorf("failed to publish encrypted DSAR archive: %w", err)
	}
	return nil
}

// encryptFile closes each PGP writer before replacing the temporary plaintext.
// The caller owns the lifetime and eventual removal of the temporary archive.
func (e *DSARExporter) encryptFile(filePath string) error {
	plaintext, err := os.ReadFile(filePath)
	if err != nil {
		return fmt.Errorf("failed to read archive for encryption: %w", err)
	}
	publicKeyFile, err := os.Open(e.publicKeyPath)
	if err != nil {
		return fmt.Errorf("failed to open recipient public key: %w", err)
	}
	defer publicKeyFile.Close()

	block, err := armor.Decode(publicKeyFile)
	if err != nil {
		return fmt.Errorf("failed to decode armored public key: %w", err)
	}
	if block.Type != openpgp.PublicKeyType {
		return fmt.Errorf("recipient key is not a PGP public key")
	}
	entity, err := openpgp.ReadEntity(packet.NewReader(block.Body))
	if err != nil {
		return fmt.Errorf("failed to parse recipient public key: %w", err)
	}

	cipherPath := filePath + ".gpg"
	cipherFile, err := os.OpenFile(cipherPath, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
	if err != nil {
		return fmt.Errorf("failed to create encrypted output: %w", err)
	}
	defer os.Remove(cipherPath)
	armored, err := armor.Encode(cipherFile, "PGP MESSAGE", nil)
	if err != nil {
		_ = cipherFile.Close()
		return fmt.Errorf("failed to start armored output: %w", err)
	}
	// A ZIP archive is binary: text-mode literal packets permit line-ending
	// normalization by recipients, corrupting otherwise valid ZIP bytes.
	writer, err := openpgp.Encrypt(armored, []*openpgp.Entity{entity}, nil, &openpgp.FileHints{IsBinary: true}, nil)
	if err != nil {
		_ = armored.Close()
		_ = cipherFile.Close()
		return fmt.Errorf("failed to initialize PGP encryption: %w", err)
	}
	if _, err := writer.Write(plaintext); err != nil {
		_ = writer.Close()
		_ = armored.Close()
		_ = cipherFile.Close()
		return fmt.Errorf("failed to write encrypted archive: %w", err)
	}
	// Finish the encrypted data packet, ASCII armor checksum and file in
	// that order. The original implementation published the file first.
	if err := writer.Close(); err != nil {
		_ = armored.Close()
		_ = cipherFile.Close()
		return fmt.Errorf("failed to finalize PGP payload: %w", err)
	}
	if err := armored.Close(); err != nil {
		_ = cipherFile.Close()
		return fmt.Errorf("failed to finalize armored PGP output: %w", err)
	}
	if err := cipherFile.Close(); err != nil {
		return fmt.Errorf("failed to close encrypted archive: %w", err)
	}

	if err := os.Remove(filePath); err != nil {
		return fmt.Errorf("failed to remove temporary plaintext archive: %w", err)
	}
	if err := os.Rename(cipherPath, filePath); err != nil {
		return fmt.Errorf("failed to replace plaintext with ciphertext: %w", err)
	}
	return nil
}

// stringPtr returns a pointer to a string
func stringPtr(s string) *string {
	return &s
}
