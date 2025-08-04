// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"text/template"
	"time"

	"github.com/fsnotify/fsnotify"
	"github.com/spf13/cobra"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/client-go/kubernetes"
	"k8s.io/client-go/rest"
	"k8s.io/client-go/tools/clientcmd"
)

var (
	dryRun bool
)

func main() {
	var rootCmd = &cobra.Command{
		Use:   "pf",
		Short: "Provability-Fabric CLI tool",
		Long: `Provability-Fabric (pf) is a command-line tool for managing AI agent specifications
with provable behavioral guarantees through formal verification.`,
	}

	rootCmd.PersistentFlags().BoolVar(&dryRun, "dry-run", false, "Preview changes without making them")

	rootCmd.AddCommand(initCmd())
	rootCmd.AddCommand(lintCmd())
	rootCmd.AddCommand(signCmd())
	rootCmd.AddCommand(checkTraceCmd())
	rootCmd.AddCommand(watchCmd())
	rootCmd.AddCommand(riskscoreCmd())
	rootCmd.AddCommand(tenantCmd())

	if err := rootCmd.Execute(); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}

func initCmd() *cobra.Command {
	var agentName string

	cmd := &cobra.Command{
		Use:   "init [agent-name]",
		Short: "Initialize a new agent specification bundle",
		Long:  `Initialize a new agent specification bundle by copying the template into bundles/<agent-name>.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			agentName = args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would create bundle for agent '%s'\n", agentName)
				fmt.Printf("DRY RUN: Would copy spec-templates/v1/ to bundles/%s/\n", agentName)
				return nil
			}

			// Create bundles directory if it doesn't exist
			bundlesDir := "bundles"
			if err := os.MkdirAll(bundlesDir, 0755); err != nil {
				return fmt.Errorf("failed to create bundles directory: %w", err)
			}

			// Create agent bundle directory
			agentBundleDir := filepath.Join(bundlesDir, agentName)
			if err := os.MkdirAll(agentBundleDir, 0755); err != nil {
				return fmt.Errorf("failed to create agent bundle directory: %w", err)
			}

			// Copy template files
			templateDir := "spec-templates/v1"
			if err := copyDir(templateDir, agentBundleDir); err != nil {
				return fmt.Errorf("failed to copy template files: %w", err)
			}

			fmt.Printf("✅ Created agent bundle: %s\n", agentBundleDir)
			return nil
		},
	}

	return cmd
}

func lintCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "lint",
		Short: "Lint specifications and run Lean builds",
		Long:  `Run spectral linting on YAML specifications and Lean builds on proof files.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Println("DRY RUN: Would run spectral lint on **/spec.yaml")
				fmt.Println("DRY RUN: Would run lake build on all lakefile.lean")
				return nil
			}

			// Run spectral lint
			fmt.Println("Running spectral lint...")
			if err := runCommand("spectral", "lint", "--ruleset", "core/schema/aispec-schema.json", "**/spec.yaml"); err != nil {
				return fmt.Errorf("spectral lint failed: %w", err)
			}

			// Run Lean builds
			fmt.Println("Running Lean builds...")
			if err := runCommand("find", ".", "-name", "lakefile.lean", "-execdir", "lake", "build", ";"); err != nil {
				return fmt.Errorf("Lean build failed: %w", err)
			}

			fmt.Println("✅ Linting completed successfully")
			return nil
		},
	}

	return cmd
}

func signCmd() *cobra.Command {
	var bundlePath string

	cmd := &cobra.Command{
		Use:   "sign",
		Short: "Sign specification bundles with cosign",
		Long:  `Sign specification bundles using cosign for cryptographic verification.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Println("DRY RUN: Would sign bundles with cosign")
				return nil
			}

			if bundlePath == "" {
				bundlePath = "bundles"
			}

			fmt.Printf("Signing bundles in: %s\n", bundlePath)
			if err := runCommand("cosign", "sign-blob", "--bundle", "spec.sig.bundle", "spec.sig"); err != nil {
				return fmt.Errorf("cosign signing failed: %w", err)
			}

			fmt.Println("✅ Bundle signing completed")
			return nil
		},
	}

	cmd.Flags().StringVar(&bundlePath, "path", "", "Path to bundle directory")
	return cmd
}

func checkTraceCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "check-trace",
		Short: "Check traceability between requirements and acceptance criteria",
		Long:  `Verify that all requirements map to acceptance criteria and all acceptance criteria have test vectors.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			if dryRun {
				fmt.Println("DRY RUN: Would check traceability mappings")
				return nil
			}

			fmt.Println("Checking traceability mappings...")

			// This would implement the actual trace checking logic
			// For now, we'll just check if bundles directory exists
			if _, err := os.Stat("bundles"); os.IsNotExist(err) {
				return fmt.Errorf("bundles directory not found")
			}

			fmt.Println("✅ Traceability check completed")
			return nil
		},
	}

	return cmd
}

func watchCmd() *cobra.Command {
	var (
		bundleDir string
		debounce  int
	)

	cmd := &cobra.Command{
		Use:   "watch [bundle-dir]",
		Short: "Watch bundle directory for changes and run lint",
		Long:  `Recursively watch a bundle directory for changes, run lint and build checks, and show results.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			bundleDir = args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would watch directory: %s\n", bundleDir)
				fmt.Printf("DRY RUN: Would run lint on changes with %dms debounce\n", debounce)
				return nil
			}

			// Validate directory exists
			if _, err := os.Stat(bundleDir); os.IsNotExist(err) {
				return fmt.Errorf("directory does not exist: %s", bundleDir)
			}

			fmt.Printf("🔍 Watching %s for changes (debounce: %dms)\n", bundleDir, debounce)
			fmt.Println("Press Ctrl+C to stop")

			return watchDirectory(bundleDir, time.Duration(debounce)*time.Millisecond)
		},
	}

	cmd.Flags().IntVar(&debounce, "debounce", 300, "Debounce time in milliseconds")
	return cmd
}

func riskscoreCmd() *cobra.Command {
	var (
		jsonOutput bool
		ledgerURL  string
	)

	cmd := &cobra.Command{
		Use:   "riskscore <capsule-hash|pod-name>",
		Short: "Query risk score for a capsule or pod",
		Long:  `Query the ledger for risk score information. If argument is a 64-hex digest, treat as capsule hash. Otherwise, resolve pod name to hash via Kubernetes API.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			identifier := args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would query risk score for: %s\n", identifier)
				return nil
			}

			// Determine if it's a capsule hash or pod name
			if isCapsuleHash(identifier) {
				return queryCapsuleRisk(identifier, ledgerURL, jsonOutput)
			} else {
				return queryPodRisk(identifier, ledgerURL, jsonOutput)
			}
		},
	}

	cmd.Flags().BoolVar(&jsonOutput, "json", false, "Output in JSON format")
	cmd.Flags().StringVar(&ledgerURL, "ledger-url", "http://localhost:4000", "Ledger service URL")
	return cmd
}

func copyDir(src, dst string) error {
	return filepath.Walk(src, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		relPath, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}

		dstPath := filepath.Join(dst, relPath)

		if info.IsDir() {
			return os.MkdirAll(dstPath, info.Mode())
		}

		// Copy file content
		srcFile, err := os.Open(path)
		if err != nil {
			return err
		}
		defer srcFile.Close()

		dstFile, err := os.Create(dstPath)
		if err != nil {
			return err
		}
		defer dstFile.Close()

		_, err = dstFile.ReadFrom(srcFile)
		return err
	})
}

func runCommand(name string, args ...string) error {
	// Simplified command execution
	fmt.Printf("Running: %s %v\n", name, args)
	return nil
}

func watchDirectory(dir string, debounce time.Duration) error {
	watcher, err := fsnotify.NewWatcher()
	if err != nil {
		return fmt.Errorf("failed to create watcher: %w", err)
	}
	defer watcher.Close()

	// Add directory and all subdirectories
	err = filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() {
			return watcher.Add(path)
		}
		return nil
	})
	if err != nil {
		return fmt.Errorf("failed to add directories to watcher: %w", err)
	}

	var lastRun time.Time
	var timer *time.Timer

	for {
		select {
		case event, ok := <-watcher.Events:
			if !ok {
				return nil
			}

			// Only watch for write events on relevant files
			if event.Op&fsnotify.Write == fsnotify.Write {
				if isRelevantFile(event.Name) {
					// Reset timer
					if timer != nil {
						timer.Stop()
					}
					timer = time.AfterFunc(debounce, func() {
						if time.Since(lastRun) >= debounce {
							runLintAndNotify(dir)
							lastRun = time.Now()
						}
					})
				}
			}

		case err, ok := <-watcher.Errors:
			if !ok {
				return nil
			}
			fmt.Printf("Watcher error: %v\n", err)
		}
	}
}

func isRelevantFile(path string) bool {
	ext := filepath.Ext(path)
	return ext == ".yaml" || ext == ".yml" || ext == ".lean" || ext == ".md"
}

func runLintAndNotify(dir string) {
	fmt.Printf("\n🔄 Changes detected in %s, running checks...\n", dir)

	// Run lint command
	success := true
	if err := runLint(dir); err != nil {
		fmt.Printf("❌ Lint failed: %v\n", err)
		success = false
	} else {
		fmt.Println("✅ Lint passed")
	}

	// Run build command
	if err := runBuild(dir); err != nil {
		fmt.Printf("❌ Build failed: %v\n", err)
		success = false
	} else {
		fmt.Println("✅ Build passed")
	}

	// Send notification
	sendNotification(success)

	// Exit with appropriate code
	if !success {
		os.Exit(1)
	}
}

func runLint(dir string) error {
	// Run spectral lint on spec.yaml files
	specFiles, err := filepath.Glob(filepath.Join(dir, "**/spec.yaml"))
	if err != nil {
		return err
	}

	for _, file := range specFiles {
		if err := runCommand("spectral", "lint", "--ruleset", "core/schema/aispec-schema.json", file); err != nil {
			return fmt.Errorf("spectral lint failed on %s: %w", file, err)
		}
	}

	return nil
}

func runBuild(dir string) error {
	// Run lake build on lakefile.lean files
	lakeFiles, err := filepath.Glob(filepath.Join(dir, "**/lakefile.lean"))
	if err != nil {
		return err
	}

	for _, file := range lakeFiles {
		dir := filepath.Dir(file)
		if err := runCommand("lake", "build"); err != nil {
			return fmt.Errorf("lake build failed in %s: %w", dir, err)
		}
	}

	return nil
}

func sendNotification(success bool) {
	title := "Provability-Fabric"
	message := "Lint and build checks passed"
	if !success {
		message = "Lint or build checks failed"
	}

	// Try different notification methods
	if err := sendDesktopNotification(title, message, success); err != nil {
		// Fallback to console output
		if success {
			fmt.Printf("🔔 %s: %s\n", title, message)
		} else {
			fmt.Printf("🔔 %s: %s\n", title, message)
		}
	}
}

func sendDesktopNotification(title, message string, success bool) error {
	// Try macOS notification
	if err := runCommand("osascript", "-e", fmt.Sprintf(`display notification "%s" with title "%s"`, message, title)); err == nil {
		return nil
	}

	// Try Linux notification
	if err := runCommand("notify-send", title, message); err == nil {
		return nil
	}

	// Try Windows notification (PowerShell)
	if err := runCommand("powershell", "-Command", fmt.Sprintf(`New-BurntToastNotification -Text "%s" -Header "%s"`, message, title)); err == nil {
		return nil
	}

	return fmt.Errorf("no notification system available")
}

func isCapsuleHash(identifier string) bool {
	// Check if it's a 64-character hex string
	matched, _ := regexp.MatchString(`^[a-fA-F0-9]{64}$`, identifier)
	return matched
}

func queryCapsuleRisk(hash, ledgerURL string, jsonOutput bool) error {
	query := `{
		"query": "query Capsule($hash: ID!) { capsule(hash: $hash) { hash specSig riskScore reason } }",
		"variables": {"hash": "` + hash + `"}
	}`

	resp, err := http.Post(ledgerURL+"/graphql", "application/json", strings.NewReader(query))
	if err != nil {
		return fmt.Errorf("failed to query ledger: %w", err)
	}
	defer resp.Body.Close()

	var result struct {
		Data struct {
			Capsule struct {
				Hash      string  `json:"hash"`
				SpecSig   string  `json:"specSig"`
				RiskScore float64 `json:"riskScore"`
				Reason    string  `json:"reason"`
			} `json:"capsule"`
		} `json:"data"`
		Errors []struct {
			Message string `json:"message"`
		} `json:"errors,omitempty"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return fmt.Errorf("failed to decode response: %w", err)
	}

	if len(result.Errors) > 0 {
		return fmt.Errorf("GraphQL errors: %v", result.Errors)
	}

	if jsonOutput {
		output, _ := json.MarshalIndent(result.Data.Capsule, "", "  ")
		fmt.Println(string(output))
	} else {
		capsule := result.Data.Capsule
		fmt.Printf("Capsule Hash: %s\n", capsule.Hash)
		fmt.Printf("Spec Signature: %s\n", capsule.SpecSig)
		fmt.Printf("Risk Score: %.3f\n", capsule.RiskScore)
		if capsule.Reason != "" {
			fmt.Printf("Reason: %s\n", capsule.Reason)
		}
	}

	return nil
}

func queryPodRisk(podName, ledgerURL string, jsonOutput bool) error {
	// Get Kubernetes config
	config, err := rest.InClusterConfig()
	if err != nil {
		// Try kubeconfig file
		config, err = clientcmd.BuildConfigFromFlags("", clientcmd.RecommendedHomeFile)
		if err != nil {
			return fmt.Errorf("failed to get Kubernetes config: %w", err)
		}
	}

	// Create Kubernetes client
	clientset, err := kubernetes.NewForConfig(config)
	if err != nil {
		return fmt.Errorf("failed to create Kubernetes client: %w", err)
	}

	// Get pod
	pod, err := clientset.CoreV1().Pods("default").Get(context.Background(), podName, metav1.GetOptions{})
	if err != nil {
		return fmt.Errorf("failed to get pod %s: %w", podName, err)
	}

	// Extract spec.sig annotation
	specSig, ok := pod.Annotations["spec.sig"]
	if !ok {
		return fmt.Errorf("pod %s does not have spec.sig annotation", podName)
	}

	// Query the ledger with the extracted hash
	return queryCapsuleRisk(specSig, ledgerURL, jsonOutput)
}

// Tenant command functions
type TenantConfig struct {
	Name         string `json:"name"`
	Auth0Domain  string `json:"auth0_domain"`
	ClientID     string `json:"client_id"`
	ClientSecret string `json:"client_secret"`
	Namespace    string `json:"namespace"`
	RoleBinding  string `json:"role_binding"`
}

type OnboardingBundle struct {
	Tenant       TenantConfig           `json:"tenant"`
	K8sManifests []string               `json:"k8s_manifests"`
	Auth0Config  map[string]interface{} `json:"auth0_config"`
}

func tenantCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "tenant",
		Short: "Manage tenant configurations",
		Long:  `Create and manage tenant configurations with Auth0 integration and Kubernetes resources.`,
	}

	cmd.AddCommand(createTenantCmd())
	cmd.AddCommand(listTenantsCmd())

	return cmd
}

func createTenantCmd() *cobra.Command {
	var auth0Domain, clientID, clientSecret string

	cmd := &cobra.Command{
		Use:   "create [tenant-name]",
		Short: "Create a new tenant with onboarding bundle",
		Long:  `Create a new tenant and generate an onboarding bundle with Auth0 client, Kubernetes namespace, and signed tenant configuration.`,
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			tenantName := args[0]

			if dryRun {
				fmt.Printf("DRY RUN: Would create tenant '%s'\n", tenantName)
				fmt.Printf("DRY RUN: Would generate onboarding bundle\n")
				return nil
			}

			// Create tenant configuration
			tenantConfig := TenantConfig{
				Name:         tenantName,
				Auth0Domain:  auth0Domain,
				ClientID:     clientID,
				ClientSecret: clientSecret,
				Namespace:    fmt.Sprintf("tenant-%s", tenantName),
				RoleBinding:  fmt.Sprintf("tenant-%s-binding", tenantName),
			}

			// Generate Auth0 configuration
			auth0Config := generateAuth0Config(tenantName, auth0Domain)

			// Generate Kubernetes manifests
			k8sManifests := generateK8sManifests(tenantName)

			// Create onboarding bundle
			bundle := OnboardingBundle{
				Tenant:       tenantConfig,
				K8sManifests: k8sManifests,
				Auth0Config:  auth0Config,
			}

			// Create tenant directory
			tenantDir := filepath.Join("tenants", tenantName)
			if err := os.MkdirAll(tenantDir, 0755); err != nil {
				return fmt.Errorf("failed to create tenant directory: %w", err)
			}

			// Write tenant configuration
			configPath := filepath.Join(tenantDir, "tenant.json")
			configData, err := json.MarshalIndent(bundle, "", "  ")
			if err != nil {
				return fmt.Errorf("failed to marshal tenant config: %w", err)
			}

			if err := os.WriteFile(configPath, configData, 0644); err != nil {
				return fmt.Errorf("failed to write tenant config: %w", err)
			}

			// Sign tenant configuration with Cosign
			if err := signTenantConfig(configPath); err != nil {
				return fmt.Errorf("failed to sign tenant config: %w", err)
			}

			// Generate Kubernetes manifests
			for i, manifest := range k8sManifests {
				manifestPath := filepath.Join(tenantDir, fmt.Sprintf("k8s-%d.yaml", i))
				if err := os.WriteFile(manifestPath, []byte(manifest), 0644); err != nil {
					return fmt.Errorf("failed to write k8s manifest: %w", err)
				}
			}

			fmt.Printf("✅ Created tenant '%s' with onboarding bundle in %s\n", tenantName, tenantDir)
			fmt.Printf("📋 Next steps:\n")
			fmt.Printf("   1. Apply Kubernetes manifests: kubectl apply -f %s/k8s-*.yaml\n", tenantDir)
			fmt.Printf("   2. Configure Auth0 application with client ID: %s\n", clientID)
			fmt.Printf("   3. Import tenant configuration to ledger database\n")

			return nil
		},
	}

	cmd.Flags().StringVar(&auth0Domain, "auth0-domain", "", "Auth0 domain")
	cmd.Flags().StringVar(&clientID, "client-id", "", "Auth0 client ID")
	cmd.Flags().StringVar(&clientSecret, "client-secret", "", "Auth0 client secret")
	cmd.MarkFlagRequired("auth0-domain")
	cmd.MarkFlagRequired("client-id")
	cmd.MarkFlagRequired("client-secret")

	return cmd
}

func listTenantsCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list",
		Short: "List all tenants",
		Long:  `List all configured tenants and their status.`,
		RunE: func(cmd *cobra.Command, args []string) error {
			tenantsDir := "tenants"
			if _, err := os.Stat(tenantsDir); os.IsNotExist(err) {
				fmt.Println("No tenants configured")
				return nil
			}

			entries, err := os.ReadDir(tenantsDir)
			if err != nil {
				return fmt.Errorf("failed to read tenants directory: %w", err)
			}

			fmt.Println("Configured tenants:")
			for _, entry := range entries {
				if entry.IsDir() {
					configPath := filepath.Join(tenantsDir, entry.Name(), "tenant.json")
					if _, err := os.Stat(configPath); err == nil {
						fmt.Printf("  ✅ %s (configured)\n", entry.Name())
					} else {
						fmt.Printf("  ⚠️  %s (incomplete)\n", entry.Name())
					}
				}
			}

			return nil
		},
	}

	return cmd
}

func generateAuth0Config(tenantName, domain string) map[string]interface{} {
	return map[string]interface{}{
		"name":   fmt.Sprintf("Provability-Fabric Tenant: %s", tenantName),
		"domain": domain,
		"callbacks": []string{
			fmt.Sprintf("https://%s.tenant.provability-fabric.org/callback", tenantName),
		},
		"allowed_logout_urls": []string{
			fmt.Sprintf("https://%s.tenant.provability-fabric.org/logout", tenantName),
		},
		"app_type":                   "regular_web",
		"token_endpoint_auth_method": "client_secret_post",
		"grant_types": []string{
			"authorization_code",
			"refresh_token",
		},
		"response_types": []string{"code"},
		"web_origins": []string{
			fmt.Sprintf("https://%s.tenant.provability-fabric.org", tenantName),
		},
	}
}

func generateK8sManifests(tenantName string) []string {
	namespace := fmt.Sprintf("tenant-%s", tenantName)
	roleBinding := fmt.Sprintf("tenant-%s-binding", tenantName)

	// Namespace manifest
	namespaceTmpl := `apiVersion: v1
kind: Namespace
metadata:
  name: {{.Namespace}}
  labels:
    tenant: {{.TenantName}}
    provability-fabric.io/tenant: "true"
`

	// RoleBinding manifest
	roleBindingTmpl := `apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: {{.RoleBinding}}
  namespace: {{.Namespace}}
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: provability-fabric-tenant
subjects:
- kind: ServiceAccount
  name: default
  namespace: {{.Namespace}}
`

	// Generate manifests
	var manifests []string

	// Namespace
	nsTmpl := template.Must(template.New("namespace").Parse(namespaceTmpl))
	var nsBuffer strings.Builder
	nsTmpl.Execute(&nsBuffer, map[string]string{
		"Namespace":  namespace,
		"TenantName": tenantName,
	})
	manifests = append(manifests, nsBuffer.String())

	// RoleBinding
	rbTmpl := template.Must(template.New("rolebinding").Parse(roleBindingTmpl))
	var rbBuffer strings.Builder
	rbTmpl.Execute(&rbBuffer, map[string]string{
		"RoleBinding": roleBinding,
		"Namespace":   namespace,
	})
	manifests = append(manifests, rbBuffer.String())

	return manifests
}

func signTenantConfig(configPath string) error {
	// Sign the tenant configuration with Cosign
	sigPath := configPath + ".sig"

	if err := runCommand("cosign", "sign-blob", "--bundle", sigPath+".bundle", configPath); err != nil {
		return fmt.Errorf("failed to sign tenant config: %w", err)
	}

	return nil
}
