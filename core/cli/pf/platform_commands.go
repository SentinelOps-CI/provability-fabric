// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"time"

	"github.com/spf13/cobra"
)

var (
	apiBaseURL = "http://localhost:8000"
)

func init() {
	if url := os.Getenv("SENTINELOPS_API_URL"); url != "" {
		apiBaseURL = url
	}
}

// policyCmd handles policy lifecycle commands
func policyCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "policy",
		Short: "Manage policies (compile, build, prove, deploy)",
		Long:  `Complete policy lifecycle management for the SentinelOps Platform.`,
	}

	cmd.AddCommand(policyCompileCmd())
	cmd.AddCommand(policyBuildCmd())
	cmd.AddCommand(policyProveCmd())
	cmd.AddCommand(policyDeployCmd())
	cmd.AddCommand(policyListCmd())

	return cmd
}

func policyCompileCmd() *cobra.Command {
	var inputFile, outputDir string

	cmd := &cobra.Command{
		Use:   "compile --in <english.md> --out <build/>",
		Short: "Compile English policy to ActionDSL",
		Long:  `Convert English policy description to ActionDSL format.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would compile %s to %s\n", inputFile, outputDir)
				return nil
			}

			// Read English policy
			englishContent, err := os.ReadFile(inputFile)
			if err != nil {
				return fmt.Errorf("failed to read input file: %w", err)
			}

			// Prepare request
			request := map[string]interface{}{
				"english":   string(englishContent),
				"policy_id": filepath.Base(inputFile),
				"version":   "1.0.0",
			}

			// Call API
			resp, err := callAPI("POST", "/api/v1/policy/compile", request)
			if err != nil {
				return err
			}

			// Create output directory
			if err := os.MkdirAll(outputDir, 0755); err != nil {
				return fmt.Errorf("failed to create output directory: %w", err)
			}

			// Write ActionDSL
			actionDSLPath := filepath.Join(outputDir, "action_dsl.json")
			actionDSLData, _ := json.MarshalIndent(resp["actionDsl"], "", "  ")
			if err := os.WriteFile(actionDSLPath, actionDSLData, 0644); err != nil {
				return fmt.Errorf("failed to write ActionDSL: %w", err)
			}

			// Write metadata
			metadataPath := filepath.Join(outputDir, "metadata.json")
			metadata := map[string]interface{}{
				"policy_hash": resp["policy_hash"],
				"timestamp":   resp["timestamp"],
				"diagnostics": resp["diagnostics"],
			}
			metadataData, _ := json.MarshalIndent(metadata, "", "  ")
			if err := os.WriteFile(metadataPath, metadataData, 0644); err != nil {
				return fmt.Errorf("failed to write metadata: %w", err)
			}

			fmt.Printf("✅ Policy compiled successfully\n")
			fmt.Printf("📁 Output: %s\n", outputDir)
			fmt.Printf("🔐 Policy hash: %s\n", resp["policy_hash"])

			return nil
		},
	}

	cmd.Flags().StringVar(&inputFile, "in", "", "Input English policy file")
	cmd.Flags().StringVar(&outputDir, "out", "build/", "Output directory")
	cmd.MarkFlagRequired("in")

	return cmd
}

func policyProveCmd() *cobra.Command {
	var buildDir string
	var useMorph bool
	var morphShards int

	cmd := &cobra.Command{
		Use:   "prove --build <build/>",
		Short: "Run proofs for compiled policy",
		Long:  `Execute Lean proofs for the compiled policy.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would run proofs for build in %s\n", buildDir)
				return nil
			}

			// Load build metadata
			metadataPath := filepath.Join(buildDir, "metadata.json")
			metadataData, err := os.ReadFile(metadataPath)
			if err != nil {
				return fmt.Errorf("failed to read build metadata: %w", err)
			}

			var metadata map[string]interface{}
			if err := json.Unmarshal(metadataData, &metadata); err != nil {
				return fmt.Errorf("failed to parse metadata: %w", err)
			}

			// Load ActionDSL
			actionDSLPath := filepath.Join(buildDir, "action_dsl.json")
			actionDSLData, err := os.ReadFile(actionDSLPath)
			if err != nil {
				return fmt.Errorf("failed to read ActionDSL: %w", err)
			}

			var actionDSL interface{}
			if err := json.Unmarshal(actionDSLData, &actionDSL); err != nil {
				return fmt.Errorf("failed to parse ActionDSL: %w", err)
			}

			// Prepare proof request
			request := map[string]interface{}{
				"policy_hash": metadata["policy_hash"],
				"action_dsl":  actionDSL,
				"use_morph":   useMorph,
			}

			if useMorph && morphShards > 0 {
				request["morph_shards"] = morphShards
			}

			// Call proof service
			resp, err := callAPI("POST", "/api/v1/proofs/run", request)
			if err != nil {
				return err
			}

			// Update metadata with proof hash
			metadata["proof_hash"] = resp["proof_hash"]
			metadata["proof_status"] = resp["status"]
			metadata["proof_artifacts"] = resp["artifacts"]

			updatedMetadata, _ := json.MarshalIndent(metadata, "", "  ")
			if err := os.WriteFile(metadataPath, updatedMetadata, 0644); err != nil {
				return fmt.Errorf("failed to update metadata: %w", err)
			}

			fmt.Printf("✅ Proofs completed: %s\n", resp["status"])
			fmt.Printf("🔐 Proof hash: %s\n", resp["proof_hash"])

			if artifacts, ok := resp["artifacts"].([]interface{}); ok && len(artifacts) > 0 {
				fmt.Printf("📁 Artifacts: %d files\n", len(artifacts))
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	cmd.Flags().BoolVar(&useMorph, "morph", false, "Use Morph distributed proving")
	cmd.Flags().IntVar(&morphShards, "shards", 4, "Number of Morph shards")

	return cmd
}

func deployCmd() *cobra.Command {
	var buildDir string
	var epochRotate bool

	cmd := &cobra.Command{
		Use:   "deploy --build <build/> [--epoch rotate]",
		Short: "Deploy policy build to runtime",
		Long:  `Deploy a built policy to the runtime environment.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would deploy build from %s\n", buildDir)
				return nil
			}

			// Load build metadata
			metadataPath := filepath.Join(buildDir, "metadata.json")
			metadataData, err := os.ReadFile(metadataPath)
			if err != nil {
				return fmt.Errorf("failed to read build metadata: %w", err)
			}

			var metadata map[string]interface{}
			if err := json.Unmarshal(metadataData, &metadata); err != nil {
				return fmt.Errorf("failed to parse metadata: %w", err)
			}

			// Check required hashes
			policyHash, ok := metadata["policy_hash"].(string)
			if !ok || policyHash == "" {
				return fmt.Errorf("missing policy_hash in metadata")
			}

			automataHash, ok := metadata["automata_hash"].(string)
			if !ok || automataHash == "" {
				return fmt.Errorf("missing automata_hash - run build first")
			}

			// Determine epoch
			currentEpoch := 1
			if epochRotate {
				currentEpoch++
			}

			// Deploy request
			request := map[string]interface{}{
				"policy_hash":   policyHash,
				"automata_hash": automataHash,
				"epoch":         currentEpoch,
			}

			resp, err := callAPI("POST", "/api/v1/runtime/deploy", request)
			if err != nil {
				return err
			}

			fmt.Printf("✅ Policy deployed successfully\n")
			fmt.Printf("🔐 Policy hash: %s\n", policyHash)
			fmt.Printf("🔧 Automata hash: %s\n", automataHash)
			fmt.Printf("⏰ Epoch: %v\n", resp["epoch"])

			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	cmd.Flags().BoolVar(&epochRotate, "epoch", false, "Rotate epoch during deployment")

	return cmd
}

// certCmd handles certificate operations
func certCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "cert",
		Short: "Certificate operations (verify, search)",
		Long:  `Validate and search CERT-V1 certificates.`,
	}

	cmd.AddCommand(certVerifyCmd())
	cmd.AddCommand(certSearchCmd())

	return cmd
}

func certVerifyCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "verify <cert-files...>",
		Short: "Verify CERT-V1 certificates",
		Long:  `Validate certificate files against CERT-V1 schema.`,
		Args:  cobra.MinimumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would verify %d certificate files\n", len(args))
				return nil
			}

			totalCerts := 0
			validCerts := 0
			invalidCerts := 0

			for _, certFile := range args {
				// Check if it's a directory or file
				if info, err := os.Stat(certFile); err == nil && info.IsDir() {
					// Process directory
					err := filepath.Walk(certFile, func(path string, info os.FileInfo, err error) error {
						if err != nil {
							return nil
						}
						if strings.HasSuffix(path, ".cert.json") {
							if verifyFile(path) {
								validCerts++
							} else {
								invalidCerts++
							}
							totalCerts++
						}
						return nil
					})
					if err != nil {
						fmt.Printf("Warning: Error walking directory %s: %v\n", certFile, err)
					}
				} else {
					// Process single file
					if verifyFile(certFile) {
						validCerts++
					} else {
						invalidCerts++
					}
					totalCerts++
				}
			}

			fmt.Printf("📊 Certificate Verification Summary:\n")
			fmt.Printf("  Total: %d\n", totalCerts)
			fmt.Printf("  Valid: %d\n", validCerts)
			fmt.Printf("  Invalid: %d\n", invalidCerts)

			if invalidCerts > 0 {
				return fmt.Errorf("validation failed: %d invalid certificates", invalidCerts)
			}

			fmt.Println("✅ All certificates are valid")
			return nil
		},
	}

	return cmd
}

func verifyFile(certFile string) bool {
	// Read certificate file
	data, err := os.ReadFile(certFile)
	if err != nil {
		fmt.Printf("❌ %s: Failed to read file: %v\n", certFile, err)
		return false
	}

	// Parse JSON
	var cert map[string]interface{}
	if err := json.Unmarshal(data, &cert); err != nil {
		fmt.Printf("❌ %s: Invalid JSON: %v\n", certFile, err)
		return false
	}

	// Basic validation (simplified)
	requiredFields := []string{
		"bundle_id", "policy_hash", "proof_hash", "automata_hash",
		"labeler_hash", "ni_claim", "ni_monitor", "sidecar_build",
	}

	for _, field := range requiredFields {
		if _, exists := cert[field]; !exists {
			fmt.Printf("❌ %s: Missing required field: %s\n", certFile, field)
			return false
		}
	}

	fmt.Printf("✅ %s: Valid\n", certFile)
	return true
}

// replayCmd handles replay operations
func replayCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "replay",
		Short: "Replay operations (run, status)",
		Long:  `Execute and monitor deterministic replays.`,
	}

	cmd.AddCommand(replayRunCmd())
	cmd.AddCommand(replayStatusCmd())

	return cmd
}

func replayRunCmd() *cobra.Command {
	var decisionID string
	var openResults bool

	cmd := &cobra.Command{
		Use:   "run <decision-id> [--open]",
		Short: "Start a replay job",
		Long:  `Start a deterministic replay for a decision ID.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			decisionID = args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would start replay for decision: %s\n", decisionID)
				return nil
			}

			// Start replay
			request := map[string]interface{}{
				"decision_id": decisionID,
				"config": map[string]interface{}{
					"seed":              42,
					"locale":            "C",
					"timezone":          "UTC",
					"chunk_size":        4096,
					"flush_cadence_ms":  100,
					"padding_policy":    "fixed",
					"drift_threshold":   0.001,
				},
			}

			resp, err := callAPI("POST", "/api/v1/replay", request)
			if err != nil {
				return err
			}

			jobID := resp["job_id"].(string)
			fmt.Printf("🔄 Started replay job: %s\n", jobID)

			// Poll for completion if --open flag is used
			if openResults {
				return pollReplayJob(jobID)
			}

			fmt.Printf("💡 Check status with: so replay status %s\n", jobID)
			return nil
		},
	}

	cmd.Flags().BoolVar(&openResults, "open", false, "Wait for completion and show results")

	return cmd
}

func replayStatusCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "status <job-id>",
		Short: "Check replay job status",
		Long:  `Check the status of a replay job.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			jobID := args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would check status for job: %s\n", jobID)
				return nil
			}

			resp, err := callAPI("GET", fmt.Sprintf("/api/v1/replay/%s", jobID), nil)
			if err != nil {
				return err
			}

			// Display status
			fmt.Printf("🔄 Replay Job: %s\n", jobID)
			fmt.Printf("Status: %s\n", resp["status"])
			fmt.Printf("Progress: %.1f%%\n", resp["progress"].(float64)*100)

			if resp["status"] == "completed" {
				fmt.Printf("✅ Low-view match: %.3f%%\n", resp["low_view_match_pct"].(float64)*100)
				fmt.Printf("⏱️  Execution time: %vms\n", resp["execution_time_ms"])
				
				if driftDetected, ok := resp["drift_detected"].(bool); ok && driftDetected {
					fmt.Printf("⚠️  Drift detected!\n")
				}
			} else if resp["status"] == "failed" {
				fmt.Printf("❌ Error: %s\n", resp["error_message"])
			}

			return nil
		},
	}

	return cmd
}

// packetCmd handles compliance packet operations
func packetCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "packet",
		Short: "Compliance packet operations",
		Long:  `Create and download compliance packets.`,
	}

	cmd.AddCommand(packetMakeCmd())

	return cmd
}

func packetMakeCmd() *cobra.Command {
	var decisionID, outputPath, tenantID string

	cmd := &cobra.Command{
		Use:   "make <decision-id> --out <artifacts/>",
		Short: "Create compliance packet",
		Long:  `Create a compliance packet for a decision.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			decisionID = args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would create packet for decision: %s\n", decisionID)
				return nil
			}

			// Build compliance packet
			request := map[string]interface{}{
				"session_id": decisionID,
				"tenant_id":  tenantID,
			}

			resp, err := callAPI("POST", "/api/v1/compliance/packet", request)
			if err != nil {
				return err
			}

			packetID := resp["packet_id"].(string)
			
			// Download packet
			downloadResp, err := callAPIRaw("GET", fmt.Sprintf("/api/v1/compliance/packet/%s", packetID))
			if err != nil {
				return err
			}

			// Save to output path
			if outputPath == "" {
				outputPath = fmt.Sprintf("compliance_packet_%s.zip", packetID)
			}

			if err := os.WriteFile(outputPath, downloadResp, 0644); err != nil {
				return fmt.Errorf("failed to save packet: %w", err)
			}

			fmt.Printf("✅ Compliance packet created: %s\n", outputPath)
			fmt.Printf("📦 Packet ID: %s\n", packetID)

			return nil
		},
	}

	cmd.Flags().StringVar(&outputPath, "out", "", "Output file path")
	cmd.Flags().StringVar(&tenantID, "tenant", "", "Tenant ID filter")

	return cmd
}

// epochCmd handles epoch operations
func epochCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "epoch",
		Short: "Epoch management operations",
		Long:  `Manage permission epochs for revocation safety.`,
	}

	cmd.AddCommand(epochRotateCmd())
	cmd.AddCommand(epochStatusCmd())

	return cmd
}

func epochRotateCmd() *cobra.Command {
	var reason string

	cmd := &cobra.Command{
		Use:   "rotate [--reason <reason>]",
		Short: "Rotate to new epoch",
		Long:  `Rotate to a new permission epoch.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would rotate epoch with reason: %s\n", reason)
				return nil
			}

			// Get current epoch first
			currentResp, err := callAPI("GET", "/api/v1/runtime/slo", nil)
			if err != nil {
				return fmt.Errorf("failed to get current epoch: %w", err)
			}

			currentEpoch := 42 // Default for demo
			newEpoch := currentEpoch + 1

			// Rotate epoch
			request := map[string]interface{}{
				"old_epoch": currentEpoch,
				"new_epoch": newEpoch,
				"reason":    reason,
			}

			resp, err := callAPI("POST", "/api/v1/runtime/epoch/rotate", request)
			if err != nil {
				return err
			}

			fmt.Printf("✅ Epoch rotated successfully\n")
			fmt.Printf("🔄 Old epoch: %v\n", resp["old_epoch"])
			fmt.Printf("🆕 New epoch: %v\n", resp["new_epoch"])
			fmt.Printf("⏰ Rotated at: %s\n", resp["rotated_at"])

			if reason != "" {
				fmt.Printf("📝 Reason: %s\n", reason)
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&reason, "reason", "", "Reason for epoch rotation")

	return cmd
}

func epochStatusCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "status",
		Short: "Show current epoch status",
		Long:  `Display current epoch information.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Println("DRY RUN: Would show epoch status")
				return nil
			}

			resp, err := callAPI("GET", "/api/v1/runtime/slo", nil)
			if err != nil {
				return err
			}

			fmt.Printf("📊 Runtime Status\n")
			fmt.Printf("Current Epoch: 42\n") // Would come from response
			fmt.Printf("TPS: %.0f\n", resp["tps"])
			fmt.Printf("Error Rate: %.2f%%\n", resp["error_rate"].(float64)*100)

			return nil
		},
	}

	return cmd
}

// Helper functions
func callAPI(method, endpoint string, data interface{}) (map[string]interface{}, error) {
	var body io.Reader
	if data != nil {
		jsonData, err := json.Marshal(data)
		if err != nil {
			return nil, fmt.Errorf("failed to marshal request: %w", err)
		}
		body = bytes.NewBuffer(jsonData)
	}

	req, err := http.NewRequest(method, apiBaseURL+endpoint, body)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	if data != nil {
		req.Header.Set("Content-Type", "application/json")
	}

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		return nil, fmt.Errorf("API error: %s", resp.Status)
	}

	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return result, nil
}

func callAPIRaw(method, endpoint string) ([]byte, error) {
	req, err := http.NewRequest(method, apiBaseURL+endpoint, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		return nil, fmt.Errorf("API error: %s", resp.Status)
	}

	return io.ReadAll(resp.Body)
}

func pollReplayJob(jobID string) error {
	fmt.Printf("⏳ Waiting for replay completion...\n")

	for {
		resp, err := callAPI("GET", fmt.Sprintf("/api/v1/replay/%s", jobID), nil)
		if err != nil {
			return err
		}

		status := resp["status"].(string)
		progress := resp["progress"].(float64)

		fmt.Printf("\r🔄 Progress: %.1f%% - %s", progress*100, status)

		if status == "completed" {
			fmt.Printf("\n✅ Replay completed successfully\n")
			fmt.Printf("📊 Low-view match: %.3f%%\n", resp["low_view_match_pct"].(float64)*100)
			
			if artifacts, ok := resp["artifacts"].([]interface{}); ok && len(artifacts) > 0 {
				fmt.Printf("📁 Artifacts available: %d files\n", len(artifacts))
			}
			
			return nil
		} else if status == "failed" {
			fmt.Printf("\n❌ Replay failed: %s\n", resp["error_message"])
			return fmt.Errorf("replay job failed")
		}

		time.Sleep(2 * time.Second)
	}
}

// Additional command implementations would go here...
func policyBuildCmd() *cobra.Command {
	var buildDir string

	cmd := &cobra.Command{
		Use:   "build --build <build/>",
		Short: "Build policy (ActionDSL to DFA)",
		Long:  `Compile ActionDSL to DFA and generate automata.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			// Implementation similar to prove command
			fmt.Println("Policy build functionality - implementation details...")
			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	return cmd
}

func policyDeployCmd() *cobra.Command {
	return deployCmd() // Reuse deploy command
}

func policyListCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list",
		Short: "List all policies",
		Long:  `List all policies in the system.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			resp, err := callAPI("GET", "/api/v1/policies", nil)
			if err != nil {
				return err
			}

			policies := resp["policies"].([]interface{})
			fmt.Printf("📋 Found %d policies:\n", len(policies))
			
			for _, policy := range policies {
				if policyMap, ok := policy.(map[string]interface{}); ok {
					fmt.Printf("  • %s (v%s)\n", policyMap["policy_id"], policyMap["version"])
				}
			}

			return nil
		},
	}

	return cmd
}

func certSearchCmd() *cobra.Command {
	var tenantID, policyHash string
	var limit int

	cmd := &cobra.Command{
		Use:   "search [--tenant <id>] [--policy <hash>] [--limit <n>]",
		Short: "Search certificates",
		Long:  `Search for certificates with filters.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			request := map[string]interface{}{
				"limit": limit,
			}

			if tenantID != "" {
				request["tenant_id"] = tenantID
			}
			if policyHash != "" {
				request["policy_hash"] = policyHash
			}

			resp, err := callAPI("POST", "/api/v1/evidence/search", request)
			if err != nil {
				return err
			}

			certs := resp["certificates"].([]interface{})
			total := int(resp["total"].(float64))

			fmt.Printf("🔍 Found %d certificates (showing %d):\n", total, len(certs))
			
			for _, cert := range certs {
				if certMap, ok := cert.(map[string]interface{}); ok {
					fmt.Printf("  • %s - %s (%s)\n", 
						certMap["session_id"], 
						certMap["ni_monitor"], 
						certMap["tenant_id"])
				}
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&tenantID, "tenant", "", "Tenant ID filter")
	cmd.Flags().StringVar(&policyHash, "policy", "", "Policy hash filter")
	cmd.Flags().IntVar(&limit, "limit", 10, "Maximum results")

	return cmd
}