// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"archive/zip"
	"encoding/json"
	"fmt"
	"io"
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

// createEncryptedZip creates an encrypted ZIP file with the DSAR data
func (e *DSARExporter) createEncryptedZip(data DSARData) error {
	// Create temporary directory for ZIP creation
	tempDir, err := os.MkdirTemp("", "dsar-export-*")
	if err != nil {
		return fmt.Errorf("failed to create temp directory: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Create JSON file with DSAR data
	jsonPath := filepath.Join(tempDir, "dsar-data.json")
	jsonData, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal DSAR data: %v", err)
	}

	if err := os.WriteFile(jsonPath, jsonData, 0644); err != nil {
		return fmt.Errorf("failed to write JSON file: %v", err)
	}

	// Create ZIP file
	zipFile, err := os.Create(e.outputPath)
	if err != nil {
		return fmt.Errorf("failed to create ZIP file: %v", err)
	}
	defer zipFile.Close()

	zipWriter := zip.NewWriter(zipFile)
	defer zipWriter.Close()

	// Add JSON file to ZIP
	jsonFile, err := os.Open(jsonPath)
	if err != nil {
		return fmt.Errorf("failed to open JSON file: %v", err)
	}
	defer jsonFile.Close()

	zipEntry, err := zipWriter.Create("dsar-data.json")
	if err != nil {
		return fmt.Errorf("failed to create ZIP entry: %v", err)
	}

	if _, err := io.Copy(zipEntry, jsonFile); err != nil {
		return fmt.Errorf("failed to copy file to ZIP: %v", err)
	}

	// Encrypt the ZIP file with recipient's public key
	if err := e.encryptFile(e.outputPath); err != nil {
		return fmt.Errorf("failed to encrypt ZIP file: %v", err)
	}

	return nil
}

// encryptFile encrypts a file using the recipient's public key
func (e *DSARExporter) encryptFile(filePath string) error {
	// Read the file to encrypt
	plaintext, err := os.ReadFile(filePath)
	if err != nil {
		return fmt.Errorf("failed to read file: %v", err)
	}

	// Read recipient's public key
	publicKeyFile, err := os.Open(e.publicKeyPath)
	if err != nil {
		return fmt.Errorf("failed to open public key file: %v", err)
	}
	defer publicKeyFile.Close()

	// Parse the public key
	block, err := armor.Decode(publicKeyFile)
	if err != nil {
		return fmt.Errorf("failed to decode armored public key: %v", err)
	}

	if block.Type != openpgp.PublicKeyType {
		return fmt.Errorf("not a public key")
	}

	entity, err := openpgp.ReadEntity(packet.NewReader(block.Body))
	if err != nil {
		return fmt.Errorf("failed to read public key entity: %v", err)
	}

	// Create encrypted file
	encryptedFile, err := os.Create(filePath + ".gpg")
	if err != nil {
		return fmt.Errorf("failed to create encrypted file: %v", err)
	}
	defer encryptedFile.Close()

	// Create armored writer
	armoredWriter, err := armor.Encode(encryptedFile, "PGP MESSAGE", nil)
	if err != nil {
		return fmt.Errorf("failed to create armored writer: %v", err)
	}
	defer armoredWriter.Close()

	// Create encrypted writer
	encryptedWriter, err := openpgp.Encrypt(armoredWriter, []*openpgp.Entity{entity}, nil, nil, nil)
	if err != nil {
		return fmt.Errorf("failed to create encrypted writer: %v", err)
	}
	defer encryptedWriter.Close()

	// Write the plaintext
	if _, err := encryptedWriter.Write(plaintext); err != nil {
		return fmt.Errorf("failed to write encrypted data: %v", err)
	}

	// Remove the unencrypted file
	if err := os.Remove(filePath); err != nil {
		return fmt.Errorf("failed to remove unencrypted file: %v", err)
	}

	// Rename encrypted file to original name
	if err := os.Rename(filePath+".gpg", filePath); err != nil {
		return fmt.Errorf("failed to rename encrypted file: %v", err)
	}

	return nil
}

// stringPtr returns a pointer to a string
func stringPtr(s string) *string {
	return &s
}
