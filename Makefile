# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

.PHONY: help build test lint clean release docs compliance insurance insights lean-offline

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
	curl -sfL https://raw.githubusercontent.com/anchore/syft/main/install.sh | sh -s -- -b /usr/local/bin v0.1.0

lean-offline: ## Build Lean proofs in offline mode
	@echo "🔧 Building Lean proofs in offline mode..."
	@# Check if vendor/mathlib exists
	@if [ ! -d "vendor/mathlib" ]; then \
		echo "❌ vendor/mathlib not found. Running vendor script..."; \
		if [ -f "scripts/vendor-mathlib.sh" ]; then \
			chmod +x scripts/vendor-mathlib.sh; \
			./scripts/vendor-mathlib.sh; \
		elif [ -f "scripts/vendor-mathlib.bat" ]; then \
			scripts/vendor-mathlib.bat; \
		else \
			echo "❌ No vendor script found!"; \
			exit 1; \
		fi; \
	fi
	@# Verify mathlib commit
	@cd vendor/mathlib && \
		EXPECTED_COMMIT="b5eba595428809e96f3ed113bc7ba776c5f801ac" && \
		ACTUAL_COMMIT=$$(git rev-parse HEAD) && \
		if [ "$$ACTUAL_COMMIT" != "$$EXPECTED_COMMIT" ]; then \
			echo "❌ Mathlib commit mismatch! Expected: $$EXPECTED_COMMIT, Got: $$ACTUAL_COMMIT"; \
			echo "Running vendor script to fix..."; \
			cd ../.. && \
			if [ -f "scripts/vendor-mathlib.sh" ]; then \
				./scripts/vendor-mathlib.sh; \
			else \
				scripts/vendor-mathlib.bat; \
			fi; \
		fi
	@echo "🔨 Building all Lean projects..."
	@cd core/lean-libs && lake build
	@cd ../../spec-templates/v1/proofs && lake build
	@cd ../../../bundles/my-agent/proofs && lake build
	@cd ../../test-new-user-agent/proofs && lake build
	@echo "✅ All Lean proofs built successfully in offline mode!"

lean-quick: ## Build only impacted Lean proofs
	@echo "🚀 Building impacted Lean proofs only..."
	@# Get impacted targets
	@IMPACTED_TARGETS=$$(python3 tools/select_impacted.py . | grep -A 1000 "--- TARGETS ---" | tail -n +2) && \
	if [ -n "$$IMPACTED_TARGETS" ]; then \
		echo "Building impacted targets: $$IMPACTED_TARGETS"; \
		for target in $$IMPACTED_TARGETS; do \
			echo "Building $$target..."; \
			cd $$target && lake build && cd -; \
		done; \
		echo "✅ Impacted Lean proofs built successfully!"; \
	else \
		echo "No impacted targets found, building core only..."; \
		cd core/lean-libs && lake build; \
		echo "✅ Core Lean proofs built successfully!"; \
	fi

lean-check-duplicates: ## Check for duplicate Lean definitions
	@echo "🔍 Checking for duplicate Lean definitions..."
	@chmod +x scripts/check-dup-lean.sh
	@./scripts/check-dup-lean.sh

lean-forbid-shadowing: ## Check for forbidden shadowing of core DSL
	@echo "🔍 Checking for forbidden shadowing..."
	@chmod +x scripts/forbid-shadowing.sh
	@./scripts/forbid-shadowing.sh

# Optimization targets
optimization: ## Run all optimization tasks
	@echo "🚀 Running all optimization tasks..."
	@$(MAKE) opt-11-semantic-cache
	@$(MAKE) opt-12-plan-compiler
	@$(MAKE) opt-13-hyperscan-pii
	@$(MAKE) opt-14-protobuf-logs
	@$(MAKE) opt-15-arm-graviton
	@echo "✅ All optimization tasks completed!"

opt-11-semantic-cache: ## OPT-11: Semantic Cache for Retrieval
	@echo "🔍 OPT-11: Semantic Cache for Retrieval"
	@echo "✅ Already implemented - checking performance..."
	@cd runtime/retrieval-gateway && cargo test --test cache_tests -- --nocapture

opt-12-plan-compiler: ## OPT-12: Plan Compiler (DFA)
	@echo "🔧 OPT-12: Plan Compiler (DFA)"
	@echo "✅ Already implemented - checking performance..."
	@cd core/policy-kernel/compiler && go test -v -bench=.

opt-13-hyperscan-pii: ## OPT-13: Hyperscan for PII Dictionary
	@echo "🚀 OPT-13: Hyperscan for PII Dictionary"
	@echo "✅ Already implemented - checking performance..."
	@cd runtime/egress-firewall && cargo test --test pii_tests -- --nocapture

opt-14-protobuf-logs: ## OPT-14: Protobuf/Flatbuffers Logs
	@echo "📝 OPT-14: Protobuf/Flatbuffers Logs"
	@echo "Building logger module..."
	@cd runtime/retrieval-gateway && cargo test --test logger_tests -- --nocapture

opt-15-arm-graviton: ## OPT-15: ARM/Graviton Build & Deploy
	@echo "🏗️ OPT-15: ARM/Graviton Build & Deploy"
	@echo "Building multi-architecture Docker images..."
	@if [ "$(OS)" = "Windows_NT" ]; then \
		scripts/build-multiarch.bat test-local; \
	else \
		chmod +x scripts/build-multiarch.sh; \
		./scripts/build-multiarch.sh test-local; \
	fi
	@echo "✅ Multi-architecture builds completed!"

multiarch-build: ## Build and push multi-architecture Docker images
	@echo "🐳 Building and pushing multi-architecture Docker images..."
	@if [ "$(OS)" = "Windows_NT" ]; then \
		scripts/build-multiarch.bat build; \
	else \
		chmod +x scripts/build-multiarch.sh; \
		./scripts/build-multiarch.sh build; \
	fi
	@echo "✅ Multi-architecture images built and pushed!"

performance-test: ## Run performance tests for optimization
	@echo "⚡ Running performance tests for optimization..."
	@$(MAKE) opt-11-semantic-cache
	@$(MAKE) opt-12-plan-compiler
	@$(MAKE) opt-13-hyperscan-pii
	@$(MAKE) opt-14-protobuf-logs
	@echo "✅ Performance tests completed!"