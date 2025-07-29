# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

.PHONY: help build test lint clean release docs compliance insurance insights

help: ## Show this help message
	@echo "Provability-Fabric Makefile"
	@echo ""
	@echo "Available targets:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

build: ## Build all components
	@echo "Building all components..."
	cd core/cli/pf && go build -o pf .
	cd runtime/sidecar-watcher && cargo build --release
	cd runtime/admission-controller && go build -o admission-controller .
	cd runtime/ledger && npm install && npm run build
	cd runtime/attestor && cargo build --release
	cd tools/specgraph && go build -o specgraph .

test: ## Run all tests
	@echo "Running tests..."
	cd core/cli/pf && go test -v ./...
	cd runtime/sidecar-watcher && cargo test
	cd runtime/admission-controller && go test -v ./...
	cd runtime/ledger && npm test
	pytest tests/integration/ -v

lint: ## Run all linters
	@echo "Running linters..."
	cd core/cli/pf && go vet ./...
	cd runtime/sidecar-watcher && cargo clippy -- -D warnings
	cd runtime/admission-controller && go vet ./...
	cd runtime/ledger && npm run lint
	spectral lint **/spec.yaml --ruleset aispec-schema.json

clean: ## Clean build artifacts
	@echo "Cleaning build artifacts..."
	rm -rf core/cli/pf/pf
	rm -rf runtime/sidecar-watcher/target
	rm -rf runtime/admission-controller/admission-controller
	rm -rf runtime/ledger/dist
	rm -rf runtime/ledger/node_modules
	rm -rf runtime/attestor/target
	rm -rf tools/specgraph/specgraph
	find . -name "*.olean" -delete
	find . -name "*.lake" -delete

docs: ## Generate documentation from spec.yaml files
	@echo "Generating documentation..."
	@# Build specdoc tool
	cd cmd/specdoc && go build -o specdoc .
	@# Create docs/generated directory
	mkdir -p docs/generated
	@# Generate docs for all spec.yaml files
	find bundles -name "spec.yaml" -exec sh -c ' \
		dir=$$(dirname "$$1") \
		basename=$$(basename "$$dir") \
		output="docs/generated/$$basename.md" \
		cmd/specdoc/specdoc generate "$$1" --out "$$output" \
	' sh {} \;
	@# Run markdownlint on generated files
	markdownlint docs/generated/*.md
	@echo "✅ Documentation generated successfully"

compliance: ## Generate EU AI Act Annex VIII documentation
	@echo "Generating EU AI Act Annex VIII documentation..."
	@# Install compliance tool dependencies
	cd tools/compliance && pip install -r requirements.txt
	@# Create compliance directory
	mkdir -p docs/compliance
	@# Generate Annex VIII docs for all bundles
	find bundles -name "spec.yaml" -exec sh -c ' \
		agent_name=$$(basename $$(dirname "$$1")) \
		output="docs/compliance/$$agent_name"_annexVIII.pdf \
		cd tools/compliance && python generate_ai_act.py "../../$$1" --out "../../$$output" \
	' sh {} \;
	@echo "✅ EU AI Act Annex VIII documentation generated successfully"

insurance: ## Run insurance premium simulation
	@echo "Running insurance premium simulation..."
	@# Install insurance simulator dependencies
	cd tools/insure && pip install -r requirements.txt
	@# Create insights directory
	mkdir -p docs/insights
	@# Run insurance simulation
	cd tools/insure && python simulator.py --days 30 --output-dir ../../docs/insights
	@echo "✅ Insurance simulation completed successfully"

insights: ## Generate weekly insights and charts
	@echo "Generating weekly insights..."
	@# Run insurance simulation
	$(MAKE) insurance
	@# Generate additional insights
	@echo "Risk analysis charts generated in docs/insights/"
	@echo "Insurance report available at docs/insights/insurance_report.md"
	@echo "Weekly insights generated successfully"

spec-deps: ## Generate spec dependency graph
	@echo "Generating spec dependency graph..."
	@# Build specgraph tool
	cd tools/specgraph && go build -o specgraph .
	@# Generate dependency graph
	tools/specgraph/specgraph mod init
	@echo "✅ Spec dependency graph generated successfully"

provenance: ## Generate SLSA v1 provenance for all images
	@echo "Generating SLSA v1 provenance..."
	@# Make script executable
	chmod +x releaser/generate-provenance.sh
	@# Generate provenance
	./releaser/generate-provenance.sh generate
	@echo "✅ SLSA v1 provenance generated successfully"

chaos: ## Run chaos engineering experiments
	@echo "Running chaos engineering experiments..."
	@# Install chaos engineering dependencies
	kubectl apply -f https://litmuschaos.github.io/litmus/2.14.0/rbac.yaml
	kubectl apply -f https://litmuschaos.github.io/litmus/2.14.0/crds.yaml
	@# Run chaos experiments
	kubectl apply -f tests/chaos/pod-network-loss.yaml
	kubectl apply -f tests/chaos/cpu-hog.yaml
	@echo "✅ Chaos engineering experiments completed"

release: ## Create a new release (bumps version, tags, and pushes)
	@echo "Creating release..."
	@if [ -z "$(VERSION)" ]; then \
		echo "Error: VERSION is required. Usage: make release VERSION=1.2.3"; \
		exit 1; \
	fi
	@echo "Creating release v$(VERSION)..."
	@# Update VERSION file
	echo "$(VERSION)" > VERSION
	@# Get current date for stable branch
	$(eval STABLE_BRANCH := stable/$(shell date +%Y.%m))
	@# Create stable branch if it doesn't exist
	git checkout -b $(STABLE_BRANCH) 2>/dev/null || git checkout $(STABLE_BRANCH)
	@# Commit version bump
	git add VERSION
	git commit -m "Bump version to $(VERSION)"
	@# Create annotated tag with Lean hash
	$(eval LEAN_HASH := $(shell find . -name "*.olean" -exec lean --hash {} \; | head -1))
	git tag -a v$(VERSION) -m "Release v$(VERSION)

lean-hash: $(LEAN_HASH)

This release includes:
- Security updates and vulnerability fixes
- Performance improvements
- Insurance-grade risk API
- SLSA v1 provenance
- Chaos engineering harness
- Real-time attestation streaming"
	@# Push changes
	git push origin $(STABLE_BRANCH)
	git push origin v$(VERSION)
	@echo "Release v$(VERSION) created successfully"

serve-docs: ## Serve documentation locally
	@echo "Serving documentation at http://localhost:8000"
	mkdocs serve

integration: ## Run integration tests
	@echo "Running integration tests..."
	pytest tests/integration/ -v

fuzz: ## Run fuzz tests
	@echo "Running fuzz tests..."
	cd runtime/sidecar-watcher/fuzz && cargo fuzz run json_actions -- -runs=1000 -max_total_time=120

bench: ## Run performance benchmarks
	@echo "Running performance benchmarks..."
	python scripts/bench.py --count 100000 --output perf-results.json

security: ## Run security scans
	@echo "Running security scans..."
	trivy fs --severity HIGH,CRITICAL .
	gosec ./core/cli/pf/... ./runtime/admission-controller/...
	cd runtime/sidecar-watcher && cargo audit
	cd runtime/ledger && npm audit --audit-level=high

install-tools: ## Install development tools
	@echo "Installing development tools..."
	go install github.com/securecodewarrior/gosec/v2/cmd/gosec@latest
	cargo install cargo-fuzz
	npm install -g @stoplight/spectral-cli
	curl -sfL https://raw.githubusercontent.com/aquasecurity/trivy/main/contrib/install.sh | sh -s -- -b /usr/local/bin v0.48.0
	curl -sfL https://raw.githubusercontent.com/anchore/syft/main/install.sh | sh -s -- -b /usr/local/bin v1.0.0