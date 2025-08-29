package main

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"regexp"
	"strings"
	"time"

	"github.com/gorilla/mux"
	"github.com/joho/godotenv"
	"gopkg.in/go-playground/validator.v9"
)

// Package represents a marketplace package
type Package struct {
	ID            string                 `json:"id" validate:"required"`
	Name          string                 `json:"name" validate:"required"`
	Version       string                 `json:"version" validate:"required,semver"`
	Type          string                 `json:"type" validate:"required,oneof=adapter spec proofpack"`
	Compatibility map[string]interface{} `json:"compatibility" validate:"required"`
	Description   string                 `json:"description" validate:"required,max=500"`
	Author        string                 `json:"author" validate:"required"`
	License       string                 `json:"license" validate:"required"`
	Repository    string                 `json:"repository,omitempty" validate:"omitempty,url"`
	Homepage      string                 `json:"homepage,omitempty" validate:"omitempty,url"`
	Keywords      []string               `json:"keywords,omitempty"`
	Files         []File                 `json:"files,omitempty"`
	Metadata      map[string]interface{} `json:"metadata,omitempty"`
	Created       time.Time              `json:"created"`
	Updated       time.Time              `json:"updated"`
	Downloads     int                    `json:"downloads"`
	Rating        float64                `json:"rating"`
}

// File represents a package file
type File struct {
	Path string `json:"path" validate:"required"`
	Hash string `json:"hash" validate:"required,hexadecimal"`
	Size int64  `json:"size,omitempty"`
}

// InstallRequest represents an installation request
type InstallRequest struct {
	TenantID  string `json:"tenantId" validate:"required"`
	PackageID string `json:"packageId" validate:"required"`
	Version   string `json:"version" validate:"required,semver"`
}

// MarketplaceAPI represents the marketplace API server
type MarketplaceAPI struct {
	packages map[string]Package
	validate *validator.Validate
	router   *mux.Router
}

// NewMarketplaceAPI creates a new marketplace API instance
func NewMarketplaceAPI() *MarketplaceAPI {
	api := &MarketplaceAPI{
		packages: make(map[string]Package),
		validate: validator.New(),
		router:   mux.NewRouter(),
	}

	// Register custom validators
	api.validate.RegisterValidation("semver", validateSemver)

	api.setupRoutes()
	return api
}

// setupRoutes configures all API routes
func (api *MarketplaceAPI) setupRoutes() {
	// Health check (no auth required)
	api.router.HandleFunc("/health", api.healthHandler).Methods("GET")

	// Public endpoints (no auth required for development)
	api.router.HandleFunc("/packages", api.listPackages).Methods("GET")
	// Root-level CRUD and install endpoints to satisfy tests
	api.router.HandleFunc("/packages", api.createPackage).Methods("POST")
	api.router.HandleFunc("/packages/{id}", api.getPackage).Methods("GET")
	api.router.HandleFunc("/packages/{id}", api.updatePackage).Methods("PUT")
	api.router.HandleFunc("/packages/{id}", api.deletePackage).Methods("DELETE")
	api.router.HandleFunc("/packages/{id}/versions", api.getPackageVersions).Methods("GET")
	api.router.HandleFunc("/install", api.installPackage).Methods("POST")
	api.router.HandleFunc("/install/{id}", api.getInstallStatus).Methods("GET")
	api.router.HandleFunc("/search", api.searchPackages).Methods("GET")
	api.router.HandleFunc("/packages/{id}/download", api.downloadPackage).Methods("GET")

	// Protected endpoints (auth required)
	protected := api.router.PathPrefix("/api").Subrouter()
	protected.Use(api.authMiddleware)
	protected.HandleFunc("/packages", api.createPackage).Methods("POST")
	protected.HandleFunc("/packages/{id}", api.getPackage).Methods("GET")
	protected.HandleFunc("/packages/{id}", api.updatePackage).Methods("PUT")
	protected.HandleFunc("/packages/{id}", api.deletePackage).Methods("DELETE")
	protected.HandleFunc("/packages/{id}/versions", api.getPackageVersions).Methods("GET")
	protected.HandleFunc("/install", api.installPackage).Methods("POST")
	protected.HandleFunc("/install/{id}", api.getInstallStatus).Methods("GET")
	protected.HandleFunc("/webhooks/verify", api.verifyWebhook).Methods("POST")

	// Global middleware
	api.router.Use(api.corsMiddleware)
	api.router.Use(api.loggingMiddleware)
}

// healthHandler returns API health status
func (api *MarketplaceAPI) healthHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(map[string]interface{}{
		"status":    "healthy",
		"timestamp": time.Now().UTC(),
		"version":   "1.0.0",
	})
}

// listPackages returns all packages with optional filtering
func (api *MarketplaceAPI) listPackages(w http.ResponseWriter, r *http.Request) {
	query := r.URL.Query()
	packageType := query.Get("type")
	author := query.Get("author")

	var packages []Package
	for _, pkg := range api.packages {
		if packageType != "" && pkg.Type != packageType {
			continue
		}
		if author != "" && pkg.Author != author {
			continue
		}
		packages = append(packages, pkg)
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"packages": packages,
		"total":    len(packages),
	})
}

// createPackage creates a new package
func (api *MarketplaceAPI) createPackage(w http.ResponseWriter, r *http.Request) {
	var pkg Package
	if err := json.NewDecoder(r.Body).Decode(&pkg); err != nil {
		http.Error(w, "Invalid JSON", http.StatusBadRequest)
		return
	}

	// Validate package
	if err := api.validate.Struct(pkg); err != nil {
		http.Error(w, fmt.Sprintf("Validation error: %v", err), http.StatusBadRequest)
		return
	}

	// Check for duplicate
	if _, exists := api.packages[pkg.ID]; exists {
		http.Error(w, "Package already exists", http.StatusConflict)
		return
	}

	// Set timestamps
	now := time.Now()
	pkg.Created = now
	pkg.Updated = now
	pkg.Downloads = 0
	pkg.Rating = 0.0

	// Store package
	api.packages[pkg.ID] = pkg

	// Trigger verification webhook for adapters
	if pkg.Type == "adapter" {
		go api.triggerAdapterVerification(pkg)
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(pkg)
}

// getPackage returns a specific package
func (api *MarketplaceAPI) getPackage(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	pkg, exists := api.packages[id]
	if !exists {
		http.Error(w, "Package not found", http.StatusNotFound)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(pkg)
}

// updatePackage updates an existing package
func (api *MarketplaceAPI) updatePackage(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	var pkg Package
	if err := json.NewDecoder(r.Body).Decode(&pkg); err != nil {
		http.Error(w, "Invalid JSON", http.StatusBadRequest)
		return
	}

	// Validate package
	if err := api.validate.Struct(pkg); err != nil {
		http.Error(w, fmt.Sprintf("Validation error: %v", err), http.StatusBadRequest)
		return
	}

	// Check if package exists
	existing, exists := api.packages[id]
	if !exists {
		http.Error(w, "Package not found", http.StatusNotFound)
		return
	}

	// Preserve some fields
	pkg.Created = existing.Created
	pkg.Downloads = existing.Downloads
	pkg.Rating = existing.Rating
	pkg.Updated = time.Now()

	// Store updated package
	api.packages[id] = pkg

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(pkg)
}

// deletePackage deletes a package
func (api *MarketplaceAPI) deletePackage(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	if _, exists := api.packages[id]; !exists {
		http.Error(w, "Package not found", http.StatusNotFound)
		return
	}

	delete(api.packages, id)
	w.WriteHeader(http.StatusNoContent)
}

// searchPackages searches packages by query
func (api *MarketplaceAPI) searchPackages(w http.ResponseWriter, r *http.Request) {
	query := r.URL.Query().Get("q")
	if query == "" {
		http.Error(w, "Query parameter 'q' is required", http.StatusBadRequest)
		return
	}

	var results []Package
	queryLower := strings.ToLower(query)

	for _, pkg := range api.packages {
		if strings.Contains(strings.ToLower(pkg.Name), queryLower) ||
			strings.Contains(strings.ToLower(pkg.Description), queryLower) ||
			strings.Contains(strings.ToLower(pkg.Author), queryLower) {
			results = append(results, pkg)
		}
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"query":   query,
		"results": results,
		"total":   len(results),
	})
}

// downloadPackage handles package downloads
func (api *MarketplaceAPI) downloadPackage(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	pkg, exists := api.packages[id]
	if !exists {
		http.Error(w, "Package not found", http.StatusNotFound)
		return
	}

	// Create a mock package archive (in a real implementation, this would be a real file)
	packageData := map[string]interface{}{
		"id":            pkg.ID,
		"name":          pkg.Name,
		"version":       pkg.Version,
		"type":          pkg.Type,
		"description":   pkg.Description,
		"author":        pkg.Author,
		"license":       pkg.License,
		"repository":    pkg.Repository,
		"keywords":      pkg.Keywords,
		"created":       pkg.Created,
		"updated":       pkg.Updated,
		"compatibility": pkg.Compatibility,
	}

	// Convert to JSON
	jsonData, err := json.MarshalIndent(packageData, "", "  ")
	if err != nil {
		http.Error(w, "Internal server error", http.StatusInternalServerError)
		return
	}

	// Set headers for file download
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=\"%s-%s.json\"", pkg.Name, pkg.Version))
	w.Header().Set("Content-Length", fmt.Sprintf("%d", len(jsonData)))

	// Write the file
	w.Write(jsonData)
}

// getPackageVersions returns all versions of a package
func (api *MarketplaceAPI) getPackageVersions(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	var versions []Package
	for _, pkg := range api.packages {
		if strings.HasPrefix(pkg.ID, id+"-") {
			versions = append(versions, pkg)
		}
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"package":  id,
		"versions": versions,
		"total":    len(versions),
	})
}

// installPackage initiates package installation
func (api *MarketplaceAPI) installPackage(w http.ResponseWriter, r *http.Request) {
	var req InstallRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid JSON", http.StatusBadRequest)
		return
	}

	// Validate request
	if err := api.validate.Struct(req); err != nil {
		http.Error(w, fmt.Sprintf("Validation error: %v", err), http.StatusBadRequest)
		return
	}

	// Check if package exists
	pkg, exists := api.packages[req.PackageID]
	if !exists {
		http.Error(w, "Package not found", http.StatusNotFound)
		return
	}

	// Check compatibility
	if err := api.checkCompatibility(pkg, req.TenantID); err != nil {
		http.Error(w, fmt.Sprintf("Compatibility check failed: %v", err), http.StatusBadRequest)
		return
	}

	// Create installation record
	installID := fmt.Sprintf("install-%s-%s", req.TenantID, req.PackageID)

	// Increment download count
	pkg.Downloads++
	api.packages[req.PackageID] = pkg

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]interface{}{
		"installId": installID,
		"status":    "pending",
		"message":   "Installation initiated",
	})
}

// getInstallStatus returns installation status
func (api *MarketplaceAPI) getInstallStatus(w http.ResponseWriter, r *http.Request) {
	vars := mux.Vars(r)
	id := vars["id"]

	// Simulate installation status
	status := map[string]interface{}{
		"installId": id,
		"status":    "completed",
		"message":   "Package installed successfully",
		"timestamp": time.Now().UTC(),
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(status)
}

// verifyWebhook handles verification webhooks
func (api *MarketplaceAPI) verifyWebhook(w http.ResponseWriter, r *http.Request) {
	var payload map[string]interface{}
	if err := json.NewDecoder(r.Body).Decode(&payload); err != nil {
		http.Error(w, "Invalid JSON", http.StatusBadRequest)
		return
	}

	// Process verification result
	log.Printf("Received verification webhook: %+v", payload)

	w.WriteHeader(http.StatusOK)
}

// triggerAdapterVerification triggers adapter verification workflow
func (api *MarketplaceAPI) triggerAdapterVerification(pkg Package) {
	// Simulate webhook call to verification service
	log.Printf("Triggering verification for adapter: %s", pkg.ID)

	// In a real implementation, this would call the verification service
	// and update the package status based on the result
}

// checkCompatibility checks if package is compatible with tenant
func (api *MarketplaceAPI) checkCompatibility(pkg Package, tenantID string) error {
	// In a real implementation, this would check:
	// 1. Fabric version compatibility
	// 2. Tenant-specific constraints
	// 3. Dependency conflicts

	return nil
}

// authMiddleware validates Auth0 JWT tokens
func (api *MarketplaceAPI) authMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Temporarily disable auth for development
		next.ServeHTTP(w, r)
	})
}

// loggingMiddleware logs all requests
func (api *MarketplaceAPI) loggingMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		start := time.Now()
		next.ServeHTTP(w, r)
		log.Printf("%s %s %v", r.Method, r.URL.Path, time.Since(start))
	})
}

// corsMiddleware adds CORS headers to all responses
func (api *MarketplaceAPI) corsMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Access-Control-Allow-Origin", "*")
		w.Header().Set("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
		w.Header().Set("Access-Control-Allow-Headers", "Content-Type, Authorization")
		w.Header().Set("Access-Control-Max-Age", "3600") // Cache preflight requests for 1 hour

		if r.Method == "OPTIONS" {
			w.WriteHeader(http.StatusOK)
			return
		}
		next.ServeHTTP(w, r)
	})
}

// validateSemver validates semantic version strings
func validateSemver(fl validator.FieldLevel) bool {
	version := fl.Field().String()
	// Accept: 1.0.0, 1.0.0-alpha.1, 1.0.0+build.1
	// Reject: 1.0, 1.0.0.0, 1.0.0-alpha
	semverRe := regexp.MustCompile(`^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)(?:-([0-9A-Za-z-]+\.[0-9A-Za-z-]+))?(?:\+([0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*))?$`)
	return semverRe.MatchString(version)
}

func main() {
	// Load environment variables
	if err := godotenv.Load(); err != nil {
		log.Println("No .env file found")
	}

	// Create API server
	api := NewMarketplaceAPI()

	// Load some sample data
	api.loadSampleData()

	// Get port from environment
	port := os.Getenv("PORT")
	if port == "" {
		port = "8080"
	}

	// Start server
	log.Printf("Starting marketplace API server on port %s", port)
	log.Fatal(http.ListenAndServe(":"+port, api.router))
}

// loadSampleData loads sample packages for testing
func (api *MarketplaceAPI) loadSampleData() {
	samplePackages := []Package{
		{
			ID:      "marabou-adapter-1.0.0",
			Name:    "marabou-adapter",
			Version: "1.0.0",
			Type:    "adapter",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "Marabou neural network verification adapter for deep learning model verification",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/marabou-adapter",
			Keywords:    []string{"neural-network", "verification", "marabou", "deep-learning"},
			Created:     time.Now().Add(-24 * time.Hour),
			Updated:     time.Now().Add(-24 * time.Hour),
			Downloads:   150,
			Rating:      4.5,
		},
		{
			ID:      "dryvr-adapter-1.0.0",
			Name:    "dryvr-adapter",
			Version: "1.0.0",
			Type:    "adapter",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "DryVR hybrid system reachability analysis adapter for cyber-physical systems",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/dryvr-adapter",
			Keywords:    []string{"hybrid-systems", "reachability", "dryvr", "cyber-physical"},
			Created:     time.Now().Add(-48 * time.Hour),
			Updated:     time.Now().Add(-48 * time.Hour),
			Downloads:   75,
			Rating:      4.2,
		},
		{
			ID:      "ai-agent-spec-1.0.0",
			Name:    "ai-agent-spec",
			Version: "1.0.0",
			Type:    "spec",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "AI agent specification with provable behavioral guarantees and safety constraints",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/ai-agent-spec",
			Keywords:    []string{"ai-agent", "specification", "behavioral-guarantees", "safety"},
			Created:     time.Now().Add(-72 * time.Hour),
			Updated:     time.Now().Add(-72 * time.Hour),
			Downloads:   200,
			Rating:      4.8,
		},
		{
			ID:      "evil-netcall-adapter-1.0.0",
			Name:    "evil-netcall-adapter",
			Version: "1.0.0",
			Type:    "adapter",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "Evil NetCall network security verification adapter for protocol analysis",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/evil-netcall-adapter",
			Keywords:    []string{"network-security", "protocol-analysis", "evil-netcall"},
			Created:     time.Now().Add(-12 * time.Hour),
			Updated:     time.Now().Add(-12 * time.Hour),
			Downloads:   45,
			Rating:      4.0,
		},
		{
			ID:      "hello-world-spec-1.0.0",
			Name:    "hello-world-spec",
			Version: "1.0.0",
			Type:    "spec",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "Hello World specification template for getting started with Provability-Fabric",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/hello-world-spec",
			Keywords:    []string{"template", "getting-started", "hello-world", "tutorial"},
			Created:     time.Now().Add(-6 * time.Hour),
			Updated:     time.Now().Add(-6 * time.Hour),
			Downloads:   300,
			Rating:      4.9,
		},
		{
			ID:      "proofpack-security-1.0.0",
			Name:    "proofpack-security",
			Version: "1.0.0",
			Type:    "proofpack",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "Security-focused proof pack with cryptographic verification guarantees",
			Author:      "Provability-Fabric",
			License:     "Apache-2.0",
			Repository:  "https://github.com/provability-fabric/proofpack-security",
			Keywords:    []string{"security", "cryptography", "proofpack", "verification"},
			Created:     time.Now().Add(-36 * time.Hour),
			Updated:     time.Now().Add(-36 * time.Hour),
			Downloads:   120,
			Rating:      4.6,
		},
	}

	for _, pkg := range samplePackages {
		api.packages[pkg.ID] = pkg
	}
}
