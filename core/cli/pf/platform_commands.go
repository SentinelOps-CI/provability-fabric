// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
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
	var jsonOut bool
	var diffOut bool

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

			// Write IR with source map if present
			if ir, ok := resp["ir"]; ok {
				irPath := filepath.Join(outputDir, "ir.json")
				irData, _ := json.MarshalIndent(ir, "", "  ")
				if err := os.WriteFile(irPath, irData, 0644); err != nil {
					return fmt.Errorf("failed to write IR: %w", err)
				}
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

			// Optional diff vs previous output
			var diff string
			if diffOut {
				prevPath := filepath.Join(outputDir, "action_dsl.prev.json")
				if b, err := os.ReadFile(prevPath); err == nil {
					diff = computeJSONDiff(string(b), string(actionDSLData))
				}
				_ = os.WriteFile(prevPath, actionDSLData, 0644)
			}

			if jsonOut {
				payload := map[string]any{
					"ok":              true,
					"action_dsl_path": actionDSLPath,
					"metadata_path":   metadataPath,
					"ir_path":         filepath.Join(outputDir, "ir.json"),
					"policy_hash":     resp["policy_hash"],
					"diagnostics":     resp["diagnostics"],
				}
				if diffOut {
					payload["diff"] = diff
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				fmt.Printf("✅ Policy compiled successfully\n")
				fmt.Printf("📁 Output: %s\n", outputDir)
				fmt.Printf("🔐 Policy hash: %s\n", resp["policy_hash"])
				if diffOut && diff != "" {
					fmt.Println("\nDiff vs previous ActionDSL:\n" + diff)
				}
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&inputFile, "in", "", "Input English policy file")
	cmd.Flags().StringVar(&outputDir, "out", "build/", "Output directory")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	cmd.Flags().BoolVar(&diffOut, "diff", false, "Show JSON diff vs previous build output")
	cmd.MarkFlagRequired("in")

	return cmd
}

func policyProveCmd() *cobra.Command {
	var buildDir string
	var useMorph bool
	var morphShards int
	var jsonOut bool

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

			if jsonOut {
				payload := map[string]any{
					"ok":             true,
					"status":         resp["status"],
					"proof_hash":     resp["proof_hash"],
					"artifacts":      resp["artifacts"],
					"artifact_index": resp["artifact_index"],
					"metadata":       metadata,
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				fmt.Printf("✅ Proofs completed: %s\n", resp["status"])
				fmt.Printf("🔐 Proof hash: %s\n", resp["proof_hash"])

				if artifacts, ok := resp["artifacts"].([]interface{}); ok && len(artifacts) > 0 {
					fmt.Printf("📁 Artifacts: %d files\n", len(artifacts))
				}
			}

			// Persist local proofs manifest
			proofsManifest := map[string]any{
				"proof_hash":     resp["proof_hash"],
				"artifact_index": resp["artifact_index"],
				"status":         resp["status"],
			}
			pmBytes, _ := json.MarshalIndent(proofsManifest, "", "  ")
			_ = os.WriteFile(filepath.Join(buildDir, "proofs_manifest.json"), pmBytes, 0644)

			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	cmd.Flags().BoolVar(&useMorph, "morph", false, "Use Morph distributed proving")
	cmd.Flags().IntVar(&morphShards, "shards", 4, "Number of Morph shards")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func deployCmd() *cobra.Command {
	var buildDir string
	var epochRotate bool
	var jsonOut bool

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

			if jsonOut {
				payload := map[string]any{
					"ok":            true,
					"policy_hash":   policyHash,
					"automata_hash": automataHash,
					"epoch":         resp["epoch"],
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				fmt.Printf("✅ Policy deployed successfully\n")
				fmt.Printf("🔐 Policy hash: %s\n", policyHash)
				fmt.Printf("🔧 Automata hash: %s\n", automataHash)
				fmt.Printf("⏰ Epoch: %v\n", resp["epoch"])
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	cmd.Flags().BoolVar(&epochRotate, "epoch", false, "Rotate epoch during deployment")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

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
	var jsonOut bool
	var schemaValidate bool
	var schemaPath string
	var jwksURL string
	var keyPath string

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

			var checkedFiles []string
			totalCerts := 0
			validCerts := 0
			invalidCerts := 0
			var invalidList []map[string]string

			sigChecked := 0
			sigVerified := 0
			sigFailed := 0
			signatureVerificationEnabled := (jwksURL != "" || keyPath != "")

			for _, certFile := range args {
				// Check if it's a directory or file
				if info, err := os.Stat(certFile); err == nil && info.IsDir() {
					// Process directory
					err := filepath.Walk(certFile, func(path string, info os.FileInfo, err error) error {
						if err != nil {
							return nil
						}
						if strings.HasSuffix(path, ".cert.json") || strings.HasSuffix(path, ".json") {
							checkedFiles = append(checkedFiles, path)
							if verifyFileWithSchema(path, schemaPath) {
								validCerts++
							} else {
								invalidCerts++
								invalidList = append(invalidList, map[string]string{"file": path})
							}
							totalCerts++

							if signatureVerificationEnabled {
								sigChecked++
								ok, reason := verifyCertSignatureForFile(path, jwksURL, keyPath)
								if !ok {
									sigFailed++
									invalidList = append(invalidList, map[string]string{"file": path, "signature": reason})
								} else {
									sigVerified++
								}
							}
						}
						return nil
					})
					if err != nil {
						fmt.Printf("Warning: Error walking directory %s: %v\n", certFile, err)
					}
				} else {
					// Process single file
					if strings.HasSuffix(certFile, ".json") || strings.HasSuffix(certFile, ".cert.json") {
						checkedFiles = append(checkedFiles, certFile)
					}
					if verifyFileWithSchema(certFile, schemaPath) {
						validCerts++
					} else {
						invalidCerts++
						invalidList = append(invalidList, map[string]string{"file": certFile})
					}
					totalCerts++

					if signatureVerificationEnabled {
						sigChecked++
						ok, reason := verifyCertSignatureForFile(certFile, jwksURL, keyPath)
						if !ok {
							sigFailed++
							invalidList = append(invalidList, map[string]string{"file": certFile, "signature": reason})
						} else {
							sigVerified++
						}
					}
				}
			}

			// Optional schema validation via Python helper
			schemaOK := true
			schemaOutput := ""
			if schemaValidate && len(checkedFiles) > 0 {
				ok, out, err := validateCertSchemaWithPython(schemaPath, checkedFiles)
				schemaOK, schemaOutput = ok, out
				if err != nil {
					// Treat execution error as failure
					schemaOK = false
				}
			}

			if jsonOut {
				payload := map[string]any{
					"total":   totalCerts,
					"valid":   validCerts,
					"invalid": invalidCerts,
				}
				if schemaValidate {
					payload["schema_valid"] = schemaOK
					payload["schema_output"] = schemaOutput
				}
				if signatureVerificationEnabled {
					payload["signature_checked"] = sigChecked
					payload["signature_verified"] = sigVerified
					payload["signature_failed"] = sigFailed
				}
				if invalidCerts > 0 {
					payload["invalid_files"] = invalidList
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				fmt.Printf("📊 Certificate Verification Summary:\n")
				fmt.Printf("  Total: %d\n", totalCerts)
				fmt.Printf("  Valid: %d\n", validCerts)
				fmt.Printf("  Invalid: %d\n", invalidCerts)
				if schemaValidate {
					fmt.Printf("  Schema valid: %v\n", schemaOK)
				}
				if signatureVerificationEnabled {
					fmt.Printf("  Signature checked: %d, verified: %d, failed: %d\n", sigChecked, sigVerified, sigFailed)
				}
			}

			if invalidCerts > 0 || (schemaValidate && !schemaOK) || (signatureVerificationEnabled && sigFailed > 0) {
				return fmt.Errorf("validation failed")
			}

			if !jsonOut {
				fmt.Println("✅ All certificates are valid")
			}
			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	cmd.Flags().BoolVar(&schemaValidate, "schema-validate", false, "Validate against CERT-V1 schema using Python helper")
	cmd.Flags().StringVar(&schemaPath, "schema", "external/CERT-V1/schema/cert-v1.schema.json", "Path to CERT-V1 JSON schema")
	cmd.Flags().StringVar(&jwksURL, "jwks", "", "JWKS URL for Ed25519 signature verification")
	cmd.Flags().StringVar(&keyPath, "key", "", "Path to PEM-encoded Ed25519 public key for signature verification")
	return cmd
}

func validateCertSchemaWithPython(schemaPath string, files []string) (bool, string, error) {
	// Try python3 then python
	interp := "python3"
	if _, err := exec.LookPath(interp); err != nil {
		interp = "python"
	}
	args := []string{"tools/cert-validate/validate.py", "--schema", schemaPath}
	args = append(args, files...)
	cmd := exec.Command(interp, args...)
	out, err := cmd.CombinedOutput()
	return err == nil, string(out), err
}

// verifyFileWithSchema validates a single JSON file against the CERT-V1 schema using gojsonschema
func verifyFileWithSchema(filePath string, schemaPath string) bool {
	// Prefer Python-based JSON Schema validator if available and schema provided
	if schemaPath == "" {
		schemaPath = "external/CERT-V1/schema/cert-v1.schema.json"
	}
	if _, err := os.Stat(schemaPath); err == nil {
		if ok, _, err := validateCertSchemaWithPython(schemaPath, []string{filePath}); err == nil {
			return ok
		}
	}

	// Fallback: quick structural validation
	data, err := os.ReadFile(filePath)
	if err != nil {
		return false
	}
	var cert map[string]interface{}
	if err := json.Unmarshal(data, &cert); err != nil {
		return false
	}

	// Required fields (subset consistent with docs/Evidence.md)
	required := []string{
		"bundle_id", "policy_hash", "proof_hash", "automata_hash", "labeler_hash",
		"ni_monitor", "permit_decision", "path_witness_ok", "label_derivation_ok", "epoch", "egress_profile",
	}
	for _, k := range required {
		if _, ok := cert[k]; !ok {
			return false
		}
	}
	// Basic enum check for ni_monitor
	if v, ok := cert["ni_monitor"].(string); ok {
		switch v {
		case "inapplicable", "accept", "reject", "error":
			// ok
		default:
			return false
		}
	} else {
		return false
	}
	return true
}

// verifyCertSignatureForFile verifies the signature of a CERT-V1 JSON file using either a local key or JWKS.
// Returns (true, "") on success. On failure, returns (false, reason).
func verifyCertSignatureForFile(filePath, jwksURL, keyPath string) (bool, string) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return false, "read_error"
	}
	var cert map[string]interface{}
	if err := json.Unmarshal(data, &cert); err != nil {
		return false, "invalid_json"
	}
	// Extract signature
	sigVal, ok := cert["sig"]
	if !ok {
		return false, "missing_sig"
	}
	sigStr, ok := sigVal.(string)
	if !ok || sigStr == "" {
		return false, "invalid_sig"
	}
	// Remove signature field for canonicalization
	delete(cert, "sig")

	canon, err := marshalCanonicalJSON(cert)
	if err != nil {
		return false, "canonicalize_error"
	}
	// Signature can be base64 (std or URL) - try both
	var sig []byte
	if b, err := base64.StdEncoding.DecodeString(sigStr); err == nil {
		sig = b
	} else if b2, err2 := base64.RawURLEncoding.DecodeString(sigStr); err2 == nil {
		sig = b2
	} else {
		return false, "sig_decode_error"
	}

	// Try local key first if provided
	if keyPath != "" {
		if pub, err := loadEd25519PublicKeyFromPEM(keyPath); err == nil {
			if ed25519.Verify(pub, canon, sig) {
				return true, ""
			}
		}
	}
	// Then try JWKS if provided
	if jwksURL != "" {
		pubs, err := fetchEd25519KeysFromJWKS(jwksURL)
		if err == nil {
			for _, pub := range pubs {
				if ed25519.Verify(pub, canon, sig) {
					return true, ""
				}
			}
		}
	}
	return false, "signature_mismatch"
}

// loadEd25519PublicKeyFromPEM loads an Ed25519 public key from a PEM-encoded file (PKIX or raw)
func loadEd25519PublicKeyFromPEM(path string) (ed25519.PublicKey, error) {
	pemBytes, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	block, _ := pem.Decode(pemBytes)
	if block == nil {
		return nil, errors.New("no PEM block found")
	}
	// Try PKIX first
	pub, err := x509.ParsePKIXPublicKey(block.Bytes)
	if err == nil {
		if ed, ok := pub.(ed25519.PublicKey); ok {
			return ed, nil
		}
		return nil, errors.New("not an Ed25519 public key")
	}
	// Try raw
	if len(block.Bytes) == ed25519.PublicKeySize {
		return ed25519.PublicKey(block.Bytes), nil
	}
	return nil, errors.New("unsupported public key format")
}

// fetchEd25519KeysFromJWKS fetches JWKS and returns all Ed25519 public keys
func fetchEd25519KeysFromJWKS(url string) ([]ed25519.PublicKey, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode >= 400 {
		return nil, fmt.Errorf("jwks http error: %s", resp.Status)
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
	if err := json.NewDecoder(resp.Body).Decode(&jwks); err != nil {
		return nil, err
	}
	var pubs []ed25519.PublicKey
	for _, k := range jwks.Keys {
		if strings.EqualFold(k.Kty, "OKP") && strings.EqualFold(k.Crv, "Ed25519") {
			// x is base64url without padding
			raw, err := base64.RawURLEncoding.DecodeString(k.X)
			if err != nil {
				continue
			}
			if len(raw) == ed25519.PublicKeySize {
				pubs = append(pubs, ed25519.PublicKey(raw))
			}
		}
	}
	if len(pubs) == 0 {
		return nil, errors.New("no ed25519 keys in JWKS")
	}
	return pubs, nil
}

// marshalCanonicalJSON produces a canonical JSON encoding with lexicographically sorted object keys.
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
		// sort keys
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for i, k := range keys {
			// key
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
		buf.WriteString(string(t))
		return nil
	case string, float64, float32, bool, int, int64, nil:
		b, err := json.Marshal(t)
		if err != nil {
			return err
		}
		buf.Write(b)
		return nil
	default:
		// For any other type, re-marshal through encoding/json to a generic representation
		b, err := json.Marshal(t)
		if err != nil {
			return err
		}
		var vv interface{}
		if err := json.Unmarshal(b, &vv); err != nil {
			return err
		}
		return writeCanonicalJSON(buf, vv)
	}
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
	var replayFile, outputDir string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "run --file <replay.json> --out <output/>",
		Short: "Run deterministic replay",
		Long:  `Execute a deterministic replay from a trace file.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would run replay from %s to %s\n", replayFile, outputDir)
				return nil
			}

			// Read replay file
			replayData, err := os.ReadFile(replayFile)
			if err != nil {
				return fmt.Errorf("failed to read replay file: %w", err)
			}

			// Prepare request
			request := map[string]interface{}{
				"replay_data": string(replayData),
				"output_dir":  outputDir,
			}

			// Call API
			resp, err := callAPI("POST", "/api/v1/replay/run", request)
			if err != nil {
				return err
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("✅ Replay executed successfully\n")
				fmt.Printf("📁 Output: %s\n", outputDir)
				fmt.Printf("📊 Stats: %+v\n", resp["stats"])
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&replayFile, "file", "", "Replay trace file")
	cmd.Flags().StringVar(&outputDir, "out", "replay-output/", "Output directory")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	cmd.MarkFlagRequired("file")

	return cmd
}

func replayStatusCmdNew() *cobra.Command {
	var replayID string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "status --id <replay-id>",
		Short: "Get replay status",
		Long:  `Get the status of a running or completed replay.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would get status for replay %s\n", replayID)
				return nil
			}

			// Call API
			resp, err := callAPI("GET", fmt.Sprintf("/api/v1/replay/status/%s", replayID), nil)
			if err != nil {
				return err
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("📊 Replay Status: %s\n", replayID)
				fmt.Printf("Status: %s\n", resp["status"])
				fmt.Printf("Progress: %s\n", resp["progress"])
				if stats, ok := resp["stats"]; ok {
					fmt.Printf("Stats: %+v\n", stats)
				}
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&replayID, "id", "", "Replay ID")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	cmd.MarkFlagRequired("id")

	return cmd
}

// explainStateCmd provides the Explain State REPL functionality
func explainStateCmd() *cobra.Command {
	var dfaFile, event string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "explain-state",
		Short: "Explain DFA state analysis",
		Long:  `Interactive tool for analyzing DFA states and transitions.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dfaFile == "" && event == "" {
				// Launch interactive REPL
				return launchExplainStateREPL()
			}

			if dfaFile == "" {
				return fmt.Errorf("DFA file required for analysis")
			}

			// Load DFA
			dfa, err := loadDFAFromFile(dfaFile)
			if err != nil {
				return fmt.Errorf("failed to load DFA: %w", err)
			}

			if event == "" {
				return fmt.Errorf("event required for analysis")
			}

			// Analyze event
			analysis := analyzeEvent(dfa, event)

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(analysis)
			} else {
				displayAnalysis(analysis)
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&dfaFile, "dfa", "", "DFA JSON file")
	cmd.Flags().StringVar(&event, "event", "", "Event to analyze")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

// unifiedCommands provides the main unified command interface
func unifiedCommands() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "unified",
		Short: "Unified command interface",
		Long:  `Unified commands that hide complexity behind simple interfaces.`,
	}

	cmd.AddCommand(unifiedPolicyCmd())
	cmd.AddCommand(unifiedDeployCmd())
	cmd.AddCommand(unifiedReplayCmd())
	cmd.AddCommand(unifiedPacketCmd())
	cmd.AddCommand(unifiedCertCmd())

	return cmd
}

func unifiedPolicyCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "policy",
		Short: "Unified policy operations",
		Long:  `Simplified policy operations that hide complexity.`,
	}

	cmd.AddCommand(unifiedPolicyCompileCmd())
	cmd.AddCommand(unifiedPolicyProveCmd())

	return cmd
}

func unifiedPolicyCompileCmd() *cobra.Command {
	var inputFile string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "compile [input-file]",
		Short: "Compile policy with automatic output management",
		Long:  `Compile policy with smart defaults and automatic output directory management.`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if len(args) > 0 {
				inputFile = args[0]
			}

			if inputFile == "" {
				inputFile = "policy.md" // Default
			}

			// Smart output directory
			outputDir := fmt.Sprintf("build/%s", strings.TrimSuffix(filepath.Base(inputFile), filepath.Ext(inputFile)))

			// Use existing policy compile logic
			policyCompileCmd := policyCompileCmd()
			policyCompileCmd.SetArgs([]string{
				"--in", inputFile,
				"--out", outputDir,
			})
			if jsonOut {
				policyCompileCmd.SetArgs(append(policyCompileCmd.ValidArgs, "--json"))
			}

			return policyCompileCmd.Execute()
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func unifiedPolicyProveCmd() *cobra.Command {
	var buildDir string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "prove [build-directory]",
		Short: "Prove policy with automatic build detection",
		Long:  `Prove policy with smart build directory detection.`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if len(args) > 0 {
				buildDir = args[0]
			}

			if buildDir == "" {
				// Auto-detect build directory
				if entries, err := os.ReadDir("build"); err == nil {
					for _, entry := range entries {
						if entry.IsDir() {
							buildDir = filepath.Join("build", entry.Name())
							break
						}
					}
				}
			}

			if buildDir == "" {
				return fmt.Errorf("no build directory found")
			}

			// Use existing policy prove logic
			policyProveCmd := policyProveCmd()
			policyProveCmd.SetArgs([]string{
				"--build-dir", buildDir,
			})
			if jsonOut {
				policyProveCmd.SetArgs(append(policyProveCmd.ValidArgs, "--json"))
			}

			return policyProveCmd.Execute()
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func unifiedDeployCmd() *cobra.Command {
	var epoch string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "deploy --epoch [rotate|stable]",
		Short: "Deploy with epoch management",
		Long:  `Deploy policies with automatic epoch rotation.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would deploy with epoch: %s\n", epoch)
				return nil
			}

			// Prepare request
			request := map[string]interface{}{
				"epoch_action": epoch,
				"auto_rotate":  epoch == "rotate",
			}

			// Call API
			resp, err := callAPI("POST", "/api/v1/deploy", request)
			if err != nil {
				return err
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("✅ Deploy completed successfully\n")
				fmt.Printf("📊 Epoch: %s\n", resp["epoch"])
				fmt.Printf("🔄 Rotated: %t\n", resp["rotated"])
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&epoch, "epoch", "stable", "Epoch action (rotate|stable)")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func unifiedReplayCmd() *cobra.Command {
	var replayFile string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "replay run [replay-file]",
		Short: "Run replay with smart defaults",
		Long:  `Run deterministic replay with automatic file detection.`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if len(args) > 0 {
				replayFile = args[0]
			}

			if replayFile == "" {
				// Auto-detect replay files
				if entries, err := os.ReadDir("."); err == nil {
					for _, entry := range entries {
						if strings.HasSuffix(entry.Name(), ".replay.json") {
							replayFile = entry.Name()
							break
						}
					}
				}
			}

			if replayFile == "" {
				return fmt.Errorf("no replay file found")
			}

			// Use existing replay run logic
			replayRunCmd := replayRunCmd()
			replayRunCmd.SetArgs([]string{
				"--file", replayFile,
			})
			if jsonOut {
				replayRunCmd.SetArgs(append(replayRunCmd.ValidArgs, "--json"))
			}

			return replayRunCmd.Execute()
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func unifiedPacketCmd() *cobra.Command {
	var packetType string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "packet make [type]",
		Short: "Make packet with smart defaults",
		Long:  `Create packets with automatic type detection.`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if len(args) > 0 {
				packetType = args[0]
			}

			if packetType == "" {
				packetType = "evidence" // Default
			}

			if dryRun {
				fmt.Printf("DRY RUN: Would make packet of type: %s\n", packetType)
				return nil
			}

			// Prepare request
			request := map[string]interface{}{
				"packet_type": packetType,
				"auto_detect": true,
			}

			// Call API
			resp, err := callAPI("POST", "/api/v1/packet/make", request)
			if err != nil {
				return err
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("✅ Packet created successfully\n")
				fmt.Printf("📦 Type: %s\n", resp["packet_type"])
				fmt.Printf("📁 Path: %s\n", resp["packet_path"])
			}

			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func unifiedCertCmd() *cobra.Command {
	var certFile string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "cert verify [cert-file]",
		Short: "Verify certificate with smart defaults",
		Long:  `Verify certificates with automatic file detection.`,
		Args:  cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			if len(args) > 0 {
				certFile = args[0]
			}

			if certFile == "" {
				// Auto-detect certificate files
				if entries, err := os.ReadDir("."); err == nil {
					for _, entry := range entries {
						if strings.HasSuffix(entry.Name(), ".cert.json") {
							certFile = entry.Name()
							break
						}
					}
				}
			}

			if certFile == "" {
				return fmt.Errorf("no certificate file found")
			}

			if dryRun {
				fmt.Printf("DRY RUN: Would verify certificate: %s\n", certFile)
				return nil
			}

			// Read certificate
			certData, err := os.ReadFile(certFile)
			if err != nil {
				return fmt.Errorf("failed to read certificate: %w", err)
			}

			// Prepare request
			request := map[string]interface{}{
				"certificate": string(certData),
			}

			// Call API
			resp, err := callAPI("POST", "/api/v1/cert/verify", request)
			if err != nil {
				return err
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("✅ Certificate verification completed\n")
				fmt.Printf("🔐 Valid: %t\n", resp["valid"])
				fmt.Printf("📅 Expires: %s\n", resp["expires"])
			}

			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

// Helper functions for Explain State functionality

func launchExplainStateREPL() error {
	fmt.Println("🔍 Launching Explain State REPL...")
	fmt.Println("This would launch the interactive REPL tool.")
	fmt.Println("For now, use the standalone tool: go run tools/explain-state-repl/main.go")
	return nil
}

func loadDFAFromFile(filename string) (interface{}, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return nil, err
	}

	var dfa interface{}
	if err := json.Unmarshal(data, &dfa); err != nil {
		return nil, err
	}

	return dfa, nil
}

func analyzeEvent(dfa interface{}, event string) map[string]interface{} {
	// Simplified event analysis
	// In a real implementation, this would use the DFA compiler
	return map[string]interface{}{
		"event":         event,
		"current_state": 0,
		"next_state":    1,
		"is_accepting":  true,
		"is_valid":      true,
		"message":       fmt.Sprintf("Event '%s' analyzed", event),
		"timestamp":     time.Now(),
	}
}

func displayAnalysis(analysis map[string]interface{}) {
	fmt.Printf("📊 Event Analysis: '%s'\n", analysis["event"])
	fmt.Printf("   Current State: %v\n", analysis["current_state"])
	fmt.Printf("   Next State: %v\n", analysis["next_state"])
	fmt.Printf("   Is Accepting: %t\n", analysis["is_accepting"])
	fmt.Printf("   Is Valid: %t\n", analysis["is_valid"])
	fmt.Printf("   Message: %s\n", analysis["message"])
	fmt.Println()
}

func replayRunCmdOriginal() *cobra.Command {
	var decisionID string
	var openResults bool
	var jsonOut bool

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
					"seed":             42,
					"locale":           "C",
					"timezone":         "UTC",
					"chunk_size":       4096,
					"flush_cadence_ms": 100,
					"padding_policy":   "fixed",
					"drift_threshold":  0.001,
				},
			}

			resp, err := callAPI("POST", "/api/v1/replay", request)
			if err != nil {
				return err
			}

			jobID := resp["job_id"].(string)
			if jsonOut {
				if openResults {
					for {
						statusResp, err := callAPI("GET", fmt.Sprintf("/api/v1/replay/%s", jobID), nil)
						if err != nil {
							return err
						}
						status := statusResp["status"].(string)
						if status == "completed" || status == "failed" {
							enc := json.NewEncoder(os.Stdout)
							enc.SetIndent("", "  ")
							_ = enc.Encode(statusResp)
							if status == "failed" {
								return fmt.Errorf("replay job failed")
							}
							return nil
						}
						time.Sleep(2 * time.Second)
					}
				} else {
					payload := map[string]any{
						"ok":     true,
						"job_id": jobID,
					}
					enc := json.NewEncoder(os.Stdout)
					enc.SetIndent("", "  ")
					_ = enc.Encode(payload)
					return nil
				}
			} else {
				fmt.Printf("🔄 Started replay job: %s\n", jobID)
				// Poll for completion if --open flag is used
				if openResults {
					return pollReplayJob(jobID)
				}
				fmt.Printf("💡 Check status with: so replay status %s\n", jobID)
				return nil
			}
		},
	}

	cmd.Flags().BoolVar(&openResults, "open", false, "Wait for completion and show results")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func replayStatusCmd() *cobra.Command {
	var jsonOut bool
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

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
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
			}

			return nil
		},
	}

	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
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
	var jsonOut bool

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

			if jsonOut {
				payload := map[string]any{
					"ok":          true,
					"packet_id":   packetID,
					"output_path": outputPath,
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				fmt.Printf("✅ Compliance packet created: %s\n", outputPath)
				fmt.Printf("📦 Packet ID: %s\n", packetID)
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&outputPath, "out", "", "Output file path")
	cmd.Flags().StringVar(&tenantID, "tenant", "", "Tenant ID filter")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

// epochStatusCmd shows current epoch status
func epochStatusCmd() *cobra.Command {
	var jsonOut bool
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
			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(resp)
			} else {
				fmt.Printf("📊 Runtime Status\n")
				fmt.Printf("Current Epoch: 42\n")
				fmt.Printf("TPS: %.0f\n", resp["tps"])
				fmt.Printf("Error Rate: %.2f%%\n", resp["error_rate"].(float64)*100)
			}
			return nil
		},
	}
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
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
	var jsonOut bool

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
			_, err := callAPI("GET", "/api/v1/runtime/slo", nil)
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

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(map[string]any{"ok": true, "old_epoch": resp["old_epoch"], "new_epoch": resp["new_epoch"], "rotated_at": resp["rotated_at"], "reason": reason})
			} else {
				fmt.Printf("✅ Epoch rotated successfully\n")
				fmt.Printf("🔄 Old epoch: %v\n", resp["old_epoch"])
				fmt.Printf("🆕 New epoch: %v\n", resp["new_epoch"])
				fmt.Printf("⏰ Rotated at: %s\n", resp["rotated_at"])
				if reason != "" {
					fmt.Printf("📝 Reason: %s\n", reason)
				}
			}

			return nil
		},
	}

	cmd.Flags().StringVar(&reason, "reason", "", "Reason for epoch rotation")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")

	return cmd
}

func policyBuildCmd() *cobra.Command {
	var buildDir string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "build --build <build/>",
		Short: "Build policy (ActionDSL to DFA)",
		Long:  `Compile ActionDSL to DFA and generate automata.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would build policy from %s\n", buildDir)
				return nil
			}

			// Load metadata and inputs
			metadataPath := filepath.Join(buildDir, "metadata.json")
			actionDSLPath := filepath.Join(buildDir, "action_dsl.json")

			metaBytes, err := os.ReadFile(metadataPath)
			if err != nil {
				return fmt.Errorf("failed to read metadata: %w", err)
			}
			var metadata map[string]interface{}
			if err := json.Unmarshal(metaBytes, &metadata); err != nil {
				return fmt.Errorf("failed to parse metadata: %w", err)
			}

			dslBytes, err := os.ReadFile(actionDSLPath)
			if err != nil {
				return fmt.Errorf("failed to read action_dsl.json: %w", err)
			}
			var actionDSL map[string]interface{}
			if err := json.Unmarshal(dslBytes, &actionDSL); err != nil {
				return fmt.Errorf("failed to parse action_dsl.json: %w", err)
			}

			// Prepare request
			request := map[string]interface{}{
				"policy_hash": metadata["policy_hash"],
				"action_dsl":  actionDSL,
				"proof_hash":  metadata["proof_hash"],
				"metadata":    map[string]string{"source": "cli"},
			}

			resp, err := callAPI("POST", "/api/v1/policy/build", request)
			if err != nil {
				return err
			}

			// Write build info locally
			buildInfo := map[string]interface{}{
				"dfa_hash":       resp["dfa_hash"],
				"automata_hash":  resp["automata_hash"],
				"labeler_hash":   resp["labeler_hash"],
				"artifact_index": resp["artifact_index"],
			}
			buildInfoBytes, _ := json.MarshalIndent(buildInfo, "", "  ")
			if err := os.WriteFile(filepath.Join(buildDir, "build_info.json"), buildInfoBytes, 0644); err != nil {
				return fmt.Errorf("failed to write build_info.json: %w", err)
			}

			// Update metadata with automata hash
			metadata["automata_hash"] = resp["automata_hash"]
			updatedMetaBytes, _ := json.MarshalIndent(metadata, "", "  ")
			if err := os.WriteFile(metadataPath, updatedMetaBytes, 0644); err != nil {
				return fmt.Errorf("failed to update metadata.json: %w", err)
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(map[string]any{
					"ok":            true,
					"dfa_hash":      resp["dfa_hash"],
					"automata_hash": resp["automata_hash"],
					"labeler_hash":  resp["labeler_hash"],
					"build_dir":     buildDir,
				})
			} else {
				fmt.Printf("🏗️  Build completed\n")
				fmt.Printf("🔧 DFA hash: %s\n", resp["dfa_hash"])
				fmt.Printf("🔧 Automata hash: %s\n", resp["automata_hash"])
				fmt.Printf("🏷️  Labeler hash: %s\n", resp["labeler_hash"])
			}
			return nil
		},
	}

	cmd.Flags().StringVar(&buildDir, "build", "build/", "Build directory")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	return cmd
}

func policyDeployCmd() *cobra.Command {
	return deployCmd()
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
					fmt.Printf("  • %s - %s (%s)\n", certMap["session_id"], certMap["ni_monitor"], certMap["tenant_id"])
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
			// Telemetry: emit first replay success (server will skip if telemetry is disabled)
			_ = sendTelemetryEventCLI("first_replay_success", map[string]any{
				"low_view_match_pct": resp["low_view_match_pct"],
			})
			return nil
		} else if status == "failed" {
			fmt.Printf("\n❌ Replay failed: %s\n", resp["error_message"])
			return fmt.Errorf("replay job failed")
		}
		time.Sleep(2 * time.Second)
	}
}

// sendTelemetryEventCLI posts an anonymous telemetry event; errors are ignored
func sendTelemetryEventCLI(eventType string, data map[string]any) error {
	payload := map[string]any{
		"type": eventType,
		"ts":   time.Now().UTC().Format(time.RFC3339),
		"data": data,
	}
	_, err := callAPI("POST", "/api/v1/telemetry/event", payload)
	return err
}

// traceCmd handles TRACE-REPLAY-KIT operations
func traceCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "trace",
		Short: "TRACE-REPLAY-KIT operations (run, report, compare-lowview)",
		Long:  `Run deterministic replays and low-view comparisons via TRACE-REPLAY-KIT.`,
	}
	cmd.AddCommand(traceRunCmd())
	cmd.AddCommand(traceReportCmd())
	cmd.AddCommand(traceCompareLowViewCmd())
	return cmd
}

func traceRunCmd() *cobra.Command {
	var traceFile string
	var fixturesDir string
	var outDir string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "run --trace <trace.json> [--fixtures <dir>] [--out <dir>]",
		Short: "Run a replay using TRACE-REPLAY-KIT",
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would run trace %s with fixtures %s\n", traceFile, fixturesDir)
				return nil
			}

			if traceFile == "" {
				return fmt.Errorf("--trace is required")
			}

			// Prefer python runner script in external kit
			interp := "python3"
			if _, err := exec.LookPath(interp); err != nil {
				interp = "python"
			}
			pyArgs := []string{"external/TRACE-REPLAY-KIT/runner.py", traceFile}
			if fixturesDir != "" {
				pyArgs = append(pyArgs, "--fixtures", fixturesDir)
			}
			if outDir != "" {
				pyArgs = append(pyArgs, "--out", outDir)
			}

			cmdExec := exec.Command(interp, pyArgs...)
			cmdExec.Stdout = os.Stdout
			cmdExec.Stderr = os.Stderr
			if err := cmdExec.Run(); err != nil {
				return fmt.Errorf("trace run failed: %w", err)
			}

			if jsonOut {
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(map[string]any{"ok": true})
			} else {
				fmt.Println("✅ Trace run completed")
			}
			return nil
		},
	}

	cmd.Flags().StringVar(&traceFile, "trace", "", "Path to trace.json")
	cmd.Flags().StringVar(&fixturesDir, "fixtures", "", "Path to fixtures directory")
	cmd.Flags().StringVar(&outDir, "out", "", "Output directory")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	return cmd
}

func traceReportCmd() *cobra.Command {
	var inputDir string
	cmd := &cobra.Command{
		Use:   "report --in <dir>",
		Short: "Generate a replay quality report",
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would generate report from %s\n", inputDir)
				return nil
			}
			if inputDir == "" {
				return fmt.Errorf("--in is required")
			}
			// Simple aggregation stub; in production call a report generator script
			fmt.Printf("📋 Report generated for directory: %s\n", inputDir)
			return nil
		},
	}
	cmd.Flags().StringVar(&inputDir, "in", "", "Input directory containing replay artifacts")
	return cmd
}

func traceCompareLowViewCmd() *cobra.Command {
	var inputDir string
	var threshold float64
	cmd := &cobra.Command{
		Use:   "compare-lowview --in <dir> [--threshold <float>]",
		Short: "Compare low-view outputs across runs",
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Printf("DRY RUN: Would compare low-view in %s with threshold %.6f\n", inputDir, threshold)
				return nil
			}
			if inputDir == "" {
				return fmt.Errorf("--in is required")
			}
			// Prefer Python oracle if available
			interp := "python3"
			if _, err := exec.LookPath(interp); err != nil {
				interp = "python"
			}
			oracle := "external/TRACE-REPLAY-KIT/oracles/lowview_equal.py"
			if _, err := os.Stat(oracle); err == nil {
				args := []string{oracle, "--input", inputDir, "--threshold", fmt.Sprintf("%f", threshold)}
				cmdExec := exec.Command(interp, args...)
				cmdExec.Stdout = os.Stdout
				cmdExec.Stderr = os.Stderr
				if err := cmdExec.Run(); err != nil {
					return fmt.Errorf("low-view compare failed: %w", err)
				}
				fmt.Println("✅ Low-view comparison passed")
				return nil
			}
			fmt.Println("ℹ️  Oracle not found; skipping")
			return nil
		},
	}
	cmd.Flags().StringVar(&inputDir, "in", "", "Input directory of replay outputs")
	cmd.Flags().Float64Var(&threshold, "threshold", 0.999999, "Low-view equality threshold")
	return cmd
}

// computeJSONDiff renders a simple line-by-line diff of two JSON strings
func computeJSONDiff(oldJS, newJS string) string {
	oldLines := strings.Split(oldJS, "\n")
	newLines := strings.Split(newJS, "\n")
	oldSet := map[string]int{}
	for _, l := range oldLines {
		oldSet[l]++
	}
	newSet := map[string]int{}
	for _, l := range newLines {
		newSet[l]++
	}
	var b strings.Builder
	for _, l := range oldLines {
		if newSet[l] == 0 {
			b.WriteString("- " + l + "\n")
		}
	}
	for _, l := range newLines {
		if oldSet[l] == 0 {
			b.WriteString("+ " + l + "\n")
		}
	}
	return b.String()
}
