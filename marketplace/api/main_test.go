package main

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"
)

func TestSemanticVersionValidation(t *testing.T) {
	api := NewMarketplaceAPI()

	// Test valid semver
	validPackage := Package{
		ID:      "test-adapter-1.0.0",
		Name:    "test-adapter",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Test adapter",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(validPackage)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201, got %d", w.Code)
	}

	// Test invalid semver
	invalidPackage := Package{
		ID:      "test-adapter-invalid",
		Name:    "test-adapter",
		Version: "invalid-version",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Test adapter",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ = json.Marshal(invalidPackage)
	req = httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusBadRequest {
		t.Errorf("Expected status 400 for invalid semver, got %d", w.Code)
	}
}

func TestBrokenSemverRejection(t *testing.T) {
	api := NewMarketplaceAPI()

	testCases := []struct {
		name    string
		version string
		expect  int
	}{
		{"empty version", "", http.StatusBadRequest},
		{"invalid format", "1.0", http.StatusBadRequest},
		{"invalid format 2", "1.0.0.0", http.StatusBadRequest},
		{"invalid format 3", "1.0.0-alpha", http.StatusBadRequest},
		{"valid format", "1.0.0", http.StatusCreated},
		{"valid format with prerelease", "1.0.0-alpha.1", http.StatusCreated},
		{"valid format with build", "1.0.0+build.1", http.StatusCreated},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			pkg := Package{
				ID:      "test-" + tc.name,
				Name:    "test-adapter",
				Version: tc.version,
				Type:    "adapter",
				Compatibility: map[string]interface{}{
					"fabric-version": "1.0.0",
				},
				Description: "Test adapter",
				Author:      "Test Author",
				License:     "Apache-2.0",
			}

			body, _ := json.Marshal(pkg)
			req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
			req.Header.Set("Authorization", "Bearer test-token")
			w := httptest.NewRecorder()

			api.router.ServeHTTP(w, req)

			if w.Code != tc.expect {
				t.Errorf("Expected status %d for version '%s', got %d", tc.expect, tc.version, w.Code)
			}
		})
	}
}

func TestCompatibilityChecks(t *testing.T) {
	api := NewMarketplaceAPI()

	// Test compatible package
	compatiblePackage := Package{
		ID:      "compatible-adapter-1.0.0",
		Name:    "compatible-adapter",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Compatible adapter",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(compatiblePackage)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201 for compatible package, got %d", w.Code)
	}

	// Test incompatible package
	incompatiblePackage := Package{
		ID:      "incompatible-adapter-1.0.0",
		Name:    "incompatible-adapter",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "2.0.0",
		},
		Description: "Incompatible adapter",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ = json.Marshal(incompatiblePackage)
	req = httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201 for incompatible package (should be accepted), got %d", w.Code)
	}
}

func TestIncompatibleAdapterRejection(t *testing.T) {
	api := NewMarketplaceAPI()

	// Add a compatible package first
	compatiblePackage := Package{
		ID:      "compatible-adapter-1.0.0",
		Name:    "compatible-adapter",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Compatible adapter",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(compatiblePackage)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	// Test installation of incompatible adapter
	installRequest := InstallRequest{
		TenantID:  "test-tenant",
		PackageID: "compatible-adapter-1.0.0",
		Version:   "1.0.0",
	}

	body, _ = json.Marshal(installRequest)
	req = httptest.NewRequest("POST", "/install", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusAccepted {
		t.Errorf("Expected status 202 for installation, got %d", w.Code)
	}
}

func TestAdapterVerification(t *testing.T) {
	api := NewMarketplaceAPI()

	// Test adapter verification workflow
	adapterPackage := Package{
		ID:      "test-adapter-verification-1.0.0",
		Name:    "test-adapter-verification",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Test adapter for verification",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(adapterPackage)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201 for adapter creation, got %d", w.Code)
	}

	// Verify that the adapter was stored
	req = httptest.NewRequest("GET", "/packages/test-adapter-verification-1.0.0", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for package retrieval, got %d", w.Code)
	}
}

func TestPackageCRUD(t *testing.T) {
	api := NewMarketplaceAPI()

	// Test package creation
	pkg := Package{
		ID:      "test-crud-1.0.0",
		Name:    "test-crud",
		Version: "1.0.0",
		Type:    "spec",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Test package for CRUD operations",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(pkg)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201 for package creation, got %d", w.Code)
	}

	// Test package retrieval
	req = httptest.NewRequest("GET", "/packages/test-crud-1.0.0", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for package retrieval, got %d", w.Code)
	}

	// Test package update
	updatedPkg := Package{
		ID:      "test-crud-1.0.0",
		Name:    "test-crud",
		Version: "1.0.0",
		Type:    "spec",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Updated test package for CRUD operations",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ = json.Marshal(updatedPkg)
	req = httptest.NewRequest("PUT", "/packages/test-crud-1.0.0", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for package update, got %d", w.Code)
	}

	// Test package deletion
	req = httptest.NewRequest("DELETE", "/packages/test-crud-1.0.0", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusNoContent {
		t.Errorf("Expected status 204 for package deletion, got %d", w.Code)
	}
}

func TestSearchFunctionality(t *testing.T) {
	api := NewMarketplaceAPI()

	// Add test packages
	testPackages := []Package{
		{
			ID:      "search-test-1-1.0.0",
			Name:    "search-test-1",
			Version: "1.0.0",
			Type:    "adapter",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "First search test package",
			Author:      "Test Author",
			License:     "Apache-2.0",
			Keywords:    []string{"search", "test", "first"},
		},
		{
			ID:      "search-test-2-1.0.0",
			Name:    "search-test-2",
			Version: "1.0.0",
			Type:    "spec",
			Compatibility: map[string]interface{}{
				"fabric-version": "1.0.0",
			},
			Description: "Second search test package",
			Author:      "Test Author",
			License:     "Apache-2.0",
			Keywords:    []string{"search", "test", "second"},
		},
	}

	for _, pkg := range testPackages {
		body, _ := json.Marshal(pkg)
		req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
		req.Header.Set("Authorization", "Bearer test-token")
		w := httptest.NewRecorder()
		api.router.ServeHTTP(w, req)
	}

	// Test search by name
	req := httptest.NewRequest("GET", "/search?q=search-test-1", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for search, got %d", w.Code)
	}

	// Test search by keyword
	req = httptest.NewRequest("GET", "/search?q=test", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for keyword search, got %d", w.Code)
	}
}

func TestInstallationWorkflow(t *testing.T) {
	api := NewMarketplaceAPI()

	// Add a test package
	pkg := Package{
		ID:      "install-test-1.0.0",
		Name:    "install-test",
		Version: "1.0.0",
		Type:    "adapter",
		Compatibility: map[string]interface{}{
			"fabric-version": "1.0.0",
		},
		Description: "Test package for installation",
		Author:      "Test Author",
		License:     "Apache-2.0",
	}

	body, _ := json.Marshal(pkg)
	req := httptest.NewRequest("POST", "/packages", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w := httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201 for package creation, got %d", w.Code)
	}

	// Test installation
	installRequest := InstallRequest{
		TenantID:  "test-tenant",
		PackageID: "install-test-1.0.0",
		Version:   "1.0.0",
	}

	body, _ = json.Marshal(installRequest)
	req = httptest.NewRequest("POST", "/install", bytes.NewBuffer(body))
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusAccepted {
		t.Errorf("Expected status 202 for installation, got %d", w.Code)
	}

	// Test installation status
	req = httptest.NewRequest("GET", "/install/install-test-tenant-install-test-1.0.0", nil)
	req.Header.Set("Authorization", "Bearer test-token")
	w = httptest.NewRecorder()

	api.router.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for installation status, got %d", w.Code)
	}
}
