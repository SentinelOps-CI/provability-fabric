// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"context"
	"encoding/csv"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"time"

	"github.com/spf13/cobra"
)

// UsageMetrics represents tenant usage metrics
type UsageMetrics struct {
	TenantID    string    `json:"tenant_id"`
	Period      string    `json:"period"`
	CPUHours    float64   `json:"cpu_hours"`
	NetworkGB   float64   `json:"network_gb"`
	StorageGB   float64   `json:"storage_gb"`
	APIRequests int64     `json:"api_requests"`
	ProofChecks int64     `json:"proof_checks"`
	Violations  int64     `json:"violations"`
	RiskScore   float64   `json:"risk_score"`
	CostUSD     float64   `json:"cost_usd"`
	BillingTier string    `json:"billing_tier"`
	GeneratedAt time.Time `json:"generated_at"`
}

// BillingTier represents a billing tier configuration
type BillingTier struct {
	Name              string  `json:"name"`
	BasePrice         float64 `json:"base_price"`
	CPUPricePerHour   float64 `json:"cpu_price_per_hour"`
	NetworkPricePerGB float64 `json:"network_price_per_gb"`
	StoragePricePerGB float64 `json:"storage_price_per_gb"`
	APIRequestPrice   float64 `json:"api_request_price"`
	ProofCheckPrice   float64 `json:"proof_check_price"`
	ViolationPrice    float64 `json:"violation_price"`
	RiskMultiplier    float64 `json:"risk_multiplier"`
}

// CostReport represents a comprehensive cost report
type CostReport struct {
	TenantID        string        `json:"tenant_id"`
	Period          string        `json:"period"`
	TotalCost       float64       `json:"total_cost"`
	Breakdown       CostBreakdown `json:"breakdown"`
	UsageMetrics    UsageMetrics  `json:"usage_metrics"`
	Recommendations []string      `json:"recommendations"`
	GeneratedAt     time.Time     `json:"generated_at"`
}

// CostBreakdown represents detailed cost breakdown
type CostBreakdown struct {
	BaseCost       float64 `json:"base_cost"`
	CPUCost        float64 `json:"cpu_cost"`
	NetworkCost    float64 `json:"network_cost"`
	StorageCost    float64 `json:"storage_cost"`
	APICost        float64 `json:"api_cost"`
	ProofCost      float64 `json:"proof_cost"`
	ViolationCost  float64 `json:"violation_cost"`
	RiskAdjustment float64 `json:"risk_adjustment"`
}

// MeteringService handles usage metering and billing
type MeteringService struct {
	billingTiers map[string]BillingTier
	ledgerURL    string
}

// NewMeteringService creates a new metering service
func NewMeteringService(ledgerURL string) *MeteringService {
	return &MeteringService{
		ledgerURL: ledgerURL,
		billingTiers: map[string]BillingTier{
			"basic": {
				Name:              "Basic",
				BasePrice:         50.0,
				CPUPricePerHour:   0.10,
				NetworkPricePerGB: 0.05,
				StoragePricePerGB: 0.02,
				APIRequestPrice:   0.001,
				ProofCheckPrice:   0.01,
				ViolationPrice:    1.0,
				RiskMultiplier:    1.0,
			},
			"professional": {
				Name:              "Professional",
				BasePrice:         200.0,
				CPUPricePerHour:   0.08,
				NetworkPricePerGB: 0.04,
				StoragePricePerGB: 0.015,
				APIRequestPrice:   0.0008,
				ProofCheckPrice:   0.008,
				ViolationPrice:    0.8,
				RiskMultiplier:    0.9,
			},
			"enterprise": {
				Name:              "Enterprise",
				BasePrice:         500.0,
				CPUPricePerHour:   0.06,
				NetworkPricePerGB: 0.03,
				StoragePricePerGB: 0.01,
				APIRequestPrice:   0.0005,
				ProofCheckPrice:   0.005,
				ViolationPrice:    0.5,
				RiskMultiplier:    0.8,
			},
		},
	}
}

// CollectUsageMetrics collects usage metrics for a tenant
func (m *MeteringService) CollectUsageMetrics(ctx context.Context, tenantID, period string) (*UsageMetrics, error) {
	// In a real implementation, this would query the ledger service
	// For now, we'll generate sample data
	metrics := &UsageMetrics{
		TenantID:    tenantID,
		Period:      period,
		CPUHours:    float64(time.Now().Unix()%1000) / 100.0,
		NetworkGB:   float64(time.Now().Unix()%500) / 10.0,
		StorageGB:   float64(time.Now().Unix()%200) / 5.0,
		APIRequests: int64(time.Now().Unix() % 100000),
		ProofChecks: int64(time.Now().Unix() % 10000),
		Violations:  int64(time.Now().Unix() % 100),
		RiskScore:   float64(time.Now().Unix()%100) / 100.0,
		BillingTier: "professional",
		GeneratedAt: time.Now(),
	}

	// Calculate cost
	tier := m.billingTiers[metrics.BillingTier]
	metrics.CostUSD = m.calculateCost(metrics, tier)

	return metrics, nil
}

// calculateCost calculates the total cost for usage metrics
func (m *MeteringService) calculateCost(metrics *UsageMetrics, tier BillingTier) float64 {
	baseCost := tier.BasePrice
	cpuCost := metrics.CPUHours * tier.CPUPricePerHour
	networkCost := metrics.NetworkGB * tier.NetworkPricePerGB
	storageCost := metrics.StorageGB * tier.StoragePricePerGB
	apiCost := float64(metrics.APIRequests) * tier.APIRequestPrice
	proofCost := float64(metrics.ProofChecks) * tier.ProofCheckPrice
	violationCost := float64(metrics.Violations) * tier.ViolationPrice

	totalCost := baseCost + cpuCost + networkCost + storageCost + apiCost + proofCost + violationCost

	// Apply risk multiplier
	totalCost *= tier.RiskMultiplier

	return totalCost
}

// GenerateCostReport generates a comprehensive cost report
func (m *MeteringService) GenerateCostReport(ctx context.Context, tenantID, period string) (*CostReport, error) {
	metrics, err := m.CollectUsageMetrics(ctx, tenantID, period)
	if err != nil {
		return nil, fmt.Errorf("failed to collect usage metrics: %w", err)
	}

	tier := m.billingTiers[metrics.BillingTier]

	// Calculate cost breakdown
	breakdown := CostBreakdown{
		BaseCost:       tier.BasePrice,
		CPUCost:        metrics.CPUHours * tier.CPUPricePerHour,
		NetworkCost:    metrics.NetworkGB * tier.NetworkPricePerGB,
		StorageCost:    metrics.StorageGB * tier.StoragePricePerGB,
		APICost:        float64(metrics.APIRequests) * tier.APIRequestPrice,
		ProofCost:      float64(metrics.ProofChecks) * tier.ProofCheckPrice,
		ViolationCost:  float64(metrics.Violations) * tier.ViolationPrice,
		RiskAdjustment: 0.0, // Will be calculated below
	}

	// Calculate risk adjustment
	totalBaseCost := breakdown.BaseCost + breakdown.CPUCost + breakdown.NetworkCost + breakdown.StorageCost + breakdown.APICost + breakdown.ProofCost + breakdown.ViolationCost
	breakdown.RiskAdjustment = metrics.CostUSD - totalBaseCost

	// Generate recommendations
	recommendations := m.generateRecommendations(metrics, tier)

	report := &CostReport{
		TenantID:        tenantID,
		Period:          period,
		TotalCost:       metrics.CostUSD,
		Breakdown:       breakdown,
		UsageMetrics:    *metrics,
		Recommendations: recommendations,
		GeneratedAt:     time.Now(),
	}

	return report, nil
}

// generateRecommendations generates cost optimization recommendations
func (m *MeteringService) generateRecommendations(metrics *UsageMetrics, tier BillingTier) []string {
	var recommendations []string

	// Check for high violation rate
	if metrics.Violations > 50 {
		recommendations = append(recommendations, "High violation rate detected. Consider reviewing agent specifications to reduce violations.")
	}

	// Check for inefficient resource usage
	if metrics.CPUHours > 100 && metrics.APIRequests < 1000 {
		recommendations = append(recommendations, "High CPU usage with low API requests. Consider optimizing agent efficiency.")
	}

	// Check for tier upgrade opportunity
	if metrics.CostUSD > 300 && tier.Name == "basic" {
		recommendations = append(recommendations, "Consider upgrading to Professional tier for better pricing.")
	}

	// Check for tier downgrade opportunity
	if metrics.CostUSD < 100 && tier.Name == "enterprise" {
		recommendations = append(recommendations, "Consider downgrading to Professional tier to reduce costs.")
	}

	if len(recommendations) == 0 {
		recommendations = append(recommendations, "Usage patterns look optimal for current tier.")
	}

	return recommendations
}

// ExportToCSV exports cost report to CSV format
func (m *MeteringService) ExportToCSV(report *CostReport, filename string) error {
	file, err := os.Create(filename)
	if err != nil {
		return fmt.Errorf("failed to create CSV file: %w", err)
	}
	defer file.Close()

	writer := csv.NewWriter(file)
	defer writer.Flush()

	// Write header
	header := []string{
		"Tenant ID", "Period", "Total Cost (USD)", "Billing Tier",
		"CPU Hours", "CPU Cost (USD)", "Network GB", "Network Cost (USD)",
		"Storage GB", "Storage Cost (USD)", "API Requests", "API Cost (USD)",
		"Proof Checks", "Proof Cost (USD)", "Violations", "Violation Cost (USD)",
		"Risk Score", "Risk Adjustment (USD)", "Generated At",
	}
	if err := writer.Write(header); err != nil {
		return fmt.Errorf("failed to write CSV header: %w", err)
	}

	// Write data
	row := []string{
		report.TenantID,
		report.Period,
		fmt.Sprintf("%.2f", report.TotalCost),
		report.UsageMetrics.BillingTier,
		fmt.Sprintf("%.2f", report.UsageMetrics.CPUHours),
		fmt.Sprintf("%.2f", report.Breakdown.CPUCost),
		fmt.Sprintf("%.2f", report.UsageMetrics.NetworkGB),
		fmt.Sprintf("%.2f", report.Breakdown.NetworkCost),
		fmt.Sprintf("%.2f", report.UsageMetrics.StorageGB),
		fmt.Sprintf("%.2f", report.Breakdown.StorageCost),
		fmt.Sprintf("%d", report.UsageMetrics.APIRequests),
		fmt.Sprintf("%.2f", report.Breakdown.APICost),
		fmt.Sprintf("%d", report.UsageMetrics.ProofChecks),
		fmt.Sprintf("%.2f", report.Breakdown.ProofCost),
		fmt.Sprintf("%d", report.UsageMetrics.Violations),
		fmt.Sprintf("%.2f", report.Breakdown.ViolationCost),
		fmt.Sprintf("%.2f", report.UsageMetrics.RiskScore),
		fmt.Sprintf("%.2f", report.Breakdown.RiskAdjustment),
		report.GeneratedAt.Format(time.RFC3339),
	}
	if err := writer.Write(row); err != nil {
		return fmt.Errorf("failed to write CSV data: %w", err)
	}

	return nil
}

// ExportToJSON exports cost report to JSON format
func (m *MeteringService) ExportToJSON(report *CostReport, filename string) error {
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal JSON: %w", err)
	}

	if err := os.WriteFile(filename, data, 0644); err != nil {
		return fmt.Errorf("failed to write JSON file: %w", err)
	}

	return nil
}

// GenerateInvoice generates a formatted invoice
func (m *MeteringService) GenerateInvoice(report *CostReport, filename string) error {
	file, err := os.Create(filename)
	if err != nil {
		return fmt.Errorf("failed to create invoice file: %w", err)
	}
	defer file.Close()

	// Write invoice header
	fmt.Fprintf(file, "PROVABILITY-FABRIC INVOICE\n")
	fmt.Fprintf(file, "========================\n\n")
	fmt.Fprintf(file, "Tenant ID: %s\n", report.TenantID)
	fmt.Fprintf(file, "Period: %s\n", report.Period)
	fmt.Fprintf(file, "Generated: %s\n\n", report.GeneratedAt.Format("January 2, 2006"))

	// Write cost breakdown
	fmt.Fprintf(file, "COST BREAKDOWN\n")
	fmt.Fprintf(file, "==============\n")
	fmt.Fprintf(file, "Base Cost (%s tier): $%.2f\n", report.UsageMetrics.BillingTier, report.Breakdown.BaseCost)
	fmt.Fprintf(file, "CPU Usage (%.2f hours): $%.2f\n", report.UsageMetrics.CPUHours, report.Breakdown.CPUCost)
	fmt.Fprintf(file, "Network Usage (%.2f GB): $%.2f\n", report.UsageMetrics.NetworkGB, report.Breakdown.NetworkCost)
	fmt.Fprintf(file, "Storage Usage (%.2f GB): $%.2f\n", report.UsageMetrics.StorageGB, report.Breakdown.StorageCost)
	fmt.Fprintf(file, "API Requests (%d): $%.2f\n", report.UsageMetrics.APIRequests, report.Breakdown.APICost)
	fmt.Fprintf(file, "Proof Checks (%d): $%.2f\n", report.UsageMetrics.ProofChecks, report.Breakdown.ProofCost)
	fmt.Fprintf(file, "Violations (%d): $%.2f\n", report.UsageMetrics.Violations, report.Breakdown.ViolationCost)
	fmt.Fprintf(file, "Risk Adjustment: $%.2f\n\n", report.Breakdown.RiskAdjustment)

	// Write total
	fmt.Fprintf(file, "TOTAL: $%.2f\n\n", report.TotalCost)

	// Write recommendations
	fmt.Fprintf(file, "RECOMMENDATIONS\n")
	fmt.Fprintf(file, "===============\n")
	for i, rec := range report.Recommendations {
		fmt.Fprintf(file, "%d. %s\n", i+1, rec)
	}

	return nil
}

// main function and CLI setup
func main() {
	var ledgerURL string
	var outputDir string

	rootCmd := &cobra.Command{
		Use:   "pf-metering",
		Short: "Provability-Fabric usage metering and billing tool",
		Long:  `A comprehensive tool for collecting usage metrics, generating cost reports, and creating bill-ready invoices.`,
	}

	generateCmd := &cobra.Command{
		Use:   "generate [tenant-id] [period]",
		Short: "Generate cost report for a tenant",
		Args:  cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			tenantID := args[0]
			period := args[1]

			service := NewMeteringService(ledgerURL)
			report, err := service.GenerateCostReport(context.Background(), tenantID, period)
			if err != nil {
				return fmt.Errorf("failed to generate cost report: %w", err)
			}

			// Create output directory if it doesn't exist
			if err := os.MkdirAll(outputDir, 0755); err != nil {
				return fmt.Errorf("failed to create output directory: %w", err)
			}

			// Export to different formats
			baseFilename := fmt.Sprintf("%s_%s_%s", tenantID, period, time.Now().Format("20060102"))

			if err := service.ExportToJSON(report, filepath.Join(outputDir, baseFilename+".json")); err != nil {
				return fmt.Errorf("failed to export JSON: %w", err)
			}

			if err := service.ExportToCSV(report, filepath.Join(outputDir, baseFilename+".csv")); err != nil {
				return fmt.Errorf("failed to export CSV: %w", err)
			}

			if err := service.GenerateInvoice(report, filepath.Join(outputDir, baseFilename+"_invoice.txt")); err != nil {
				return fmt.Errorf("failed to generate invoice: %w", err)
			}

			log.Printf("Cost report generated successfully for tenant %s, period %s", tenantID, period)
			log.Printf("Files saved to: %s", outputDir)

			return nil
		},
	}

	generateCmd.Flags().StringVar(&ledgerURL, "ledger-url", "http://localhost:4000", "Ledger service URL")
	generateCmd.Flags().StringVar(&outputDir, "output-dir", "./billing-reports", "Output directory for reports")

	rootCmd.AddCommand(generateCmd)

	if err := rootCmd.Execute(); err != nil {
		log.Fatal(err)
	}
}
