# Developer convenience: bring up full stack locally
.PHONY: dev-up
dev-up:
	@echo "Starting platform services via docker compose..."
	docker compose up -d --build
	@echo "API Gateway: http://localhost:8000"
	@echo "Spec Service: http://localhost:8001"
	@echo "Replay Service: http://localhost:8005"

# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

.PHONY: help build test clean demo-up demo-down demo-setup install dev validate-certs lint bench security test-all helm-install helm-upgrade docs docs-serve quick-start logs rebuild lean-check-duplicates lean-forbid-shadowing vendor-mathlib no-runtime-placeholders

# ---------- Cross-platform helpers ----------
# Seconds to wait after starting containers (override with: make demo-up WAIT=10)
WAIT ?= 30

ifeq ($(OS),Windows_NT)
SLEEP        = powershell -NoProfile -Command "Start-Sleep -Seconds"
RM_RF        = powershell -NoProfile -Command "param([string[]]$$p); foreach($$x in $$p){ if (Test-Path $$x){ Remove-Item $$x -Recurse -Force -ErrorAction SilentlyContinue } }" --
FIND_PYC     = powershell -NoProfile -Command "Get-ChildItem -Recurse -Filter *.pyc -ErrorAction SilentlyContinue | Remove-Item -Force -ErrorAction SilentlyContinue; Get-ChildItem -Recurse -Directory -Filter __pycache__ -ErrorAction SilentlyContinue | Remove-Item -Recurse -Force -ErrorAction SilentlyContinue"
ECHOOK       = echo
else
SLEEP        = sleep
RM_RF        = rm -rf
FIND_PYC     = sh -lc 'find . -name "*.pyc" -delete; find . -name "__pycache__" -type d -exec rm -rf {} +'
ECHOOK       = echo
endif

# Docker Compose wrapper
DC := docker compose

# ---------- Default target ----------
help:
	@$(ECHOOK) "SentinelOps Platform - Available Commands:"
	@$(ECHOOK) ""
	@$(ECHOOK) "Development:"
	@$(ECHOOK) "  make dev             - Start development environment"
	@$(ECHOOK) "  make build           - Build all services"
	@$(ECHOOK) "  make test            - Run all tests"
	@$(ECHOOK) "  make clean           - Clean build artifacts"
	@$(ECHOOK) ""
	@$(ECHOOK) "Demo:"
	@$(ECHOOK) "  make demo-up         - Start complete demo environment"
	@$(ECHOOK) "  make demo-down       - Stop demo environment"
	@$(ECHOOK) "  make demo-setup      - Setup demo data and policies"
	@$(ECHOOK) ""
	@$(ECHOOK) "Platform:"
	@$(ECHOOK) "  make install         - Install platform locally (full mode)"
	@$(ECHOOK) "  make install-minimal - CLI + bundles only (Go required)"
	@$(ECHOOK) "  make install-standard - CLI + Rust workspace"
	@$(ECHOOK) "  make install-full    - Full install (all Python/Node deps)"
	@$(ECHOOK) "  make validate-certs  - Validate all CERT-V1 certificates"
	@$(ECHOOK) "  make lint            - Run linting on all code"
	@$(ECHOOK) ""

# ---------- Development ----------
dev:
	@$(ECHOOK) "🚀 Starting SentinelOps Platform development environment..."
	$(DC) up --build -d postgres redis
	@$(ECHOOK) "⏳ Waiting for databases to be ready..."
	@$(SLEEP) 10
	@$(ECHOOK) "🔧 Starting platform services..."
	$(DC) up --build api-gateway spec-service proof-service build-orchestrator evidence-service replay-service runtime-sidecar
	@$(ECHOOK) "✅ Development environment ready!"
	@$(ECHOOK) "🌐 Console UI: http://localhost:3000"
	@$(ECHOOK) "🔗 API Gateway: http://localhost:8000"

# ---------- Build / Test ----------
build:
	@$(ECHOOK) "🔨 Building all platform services..."
	$(DC) build

test-pcs:
	@$(ECHOOK) "Running PCS science-claim tests..."
	cd adapters/pcs && go test ./... -count=1
	cd core/cli/pf && go test ./cmd/... -count=1

test:
	@$(ECHOOK) "🧪 Running platform tests..."
	python tests/trust_fire_orchestrator.py
	@$(ECHOOK) "🧪 Running integration tests..."
	python tests/integration/test_platform_integration.py
	@$(ECHOOK) "🧪 Running demo tests..."
	cd demos/verifiable-mcp-fraud && npm test

clean:
	@$(ECHOOK) "🧹 Cleaning build artifacts..."
	$(DC) down -v
	docker system prune -f
	-$(RM_RF) build/ dist/ coverage/ .pytest_cache/
	-$(FIND_PYC)

# ---------- Demo ----------
demo-up:
	@$(ECHOOK) "🎬 Starting SentinelOps Platform Demo..."
	@$(ECHOOK) "📋 This will start the complete platform with the Verifiable MCP Fraud demo"
	$(DC) up --build -d
	@$(ECHOOK) "⏳ Waiting for services to be ready ($(WAIT)s)..."
	@$(SLEEP) $(WAIT)
	@$(ECHOOK) "🎯 Setting up demo data..."
	$(MAKE) demo-setup
	@$(ECHOOK) ""
	@$(ECHOOK) "✅ Demo environment ready!"
	@$(ECHOOK) ""
	@$(ECHOOK) "🌐 Access Points:"
	@$(ECHOOK) "  Console UI:     http://localhost:3000"
	@$(ECHOOK) "  API Gateway:    http://localhost:8000"
	@$(ECHOOK) "  Grafana:        http://localhost:3002 (admin/admin)"
	@$(ECHOOK) "  Demo App:       http://localhost:3001"
	@$(ECHOOK) ""
	@$(ECHOOK) "🎯 Demo Flow:"
	@$(ECHOOK) "  1. Open Console UI and go to Policies tab"
	@$(ECHOOK) "  2. See the fraud detection policy compiled and deployed"
	@$(ECHOOK) "  3. Go to Runtime tab to monitor live metrics"
	@$(ECHOOK) "  4. Go to Evidence tab to see CERT-V1 certificates"
	@$(ECHOOK) "  5. Run replays to verify 99.9%+ low-view equality"
	@$(ECHOOK) "  6. Download compliance packets"

demo-down:
	@$(ECHOOK) "🛑 Stopping demo environment..."
	$(DC) down
	@$(ECHOOK) "✅ Demo environment stopped"

# Run setup **inside** the verifiable-mcp-fraud container using compiled JS
demo-setup:
	@$(ECHOOK) "🎯 Setting up demo data and policies..."
	$(DC) run --rm verifiable-mcp-fraud node dist/scripts/setup-demo.js
	@$(ECHOOK) "✅ Demo setup completed"

# Optional convenience: run the demo script inside the container
demo-run:
	@$(ECHOOK) "▶️ Running demo script..."
	$(DC) run --rm verifiable-mcp-fraud node dist/scripts/run-demo.js

# ---------- Platform ----------
install: install-full

install-minimal:
	@$(ECHOOK) "Installing (minimal: CLI + bundles only)..."
	./scripts/install.sh --minimal
	@$(ECHOOK) "Minimal install completed. See docs/guides/reuse-and-extend.md"

install-standard:
	@$(ECHOOK) "Installing (standard: CLI + Rust workspace)..."
	./scripts/install.sh --standard
	@$(ECHOOK) "Standard install completed. See docs/guides/reuse-and-extend.md"

install-full:
	@$(ECHOOK) "Installing (full: all components)..."
	./scripts/install.sh --full
	@$(ECHOOK) "Platform installed successfully"

validate-certs:
	@$(ECHOOK) "🔍 Validating CERT-V1 certificates..."
	python tools/cert-validate/validate.py evidence/egress_certs/*.json evidence/certs/*/*.cert.json
	@$(ECHOOK) "✅ Certificate validation completed"

lean-check-duplicates:
	@$(ECHOOK) "🔍 Checking for duplicate Lean definitions..."
	python tools/lean_ast_hash.py .

lean-forbid-shadowing:
	@$(ECHOOK) "🔍 Checking for forbidden shadowing..."
	$(if $(filter Windows_NT,$(OS)),@$(ECHOOK) "Skipped on Windows (run scripts/forbid-shadowing.sh in Git Bash)" && exit 0,sh scripts/forbid-shadowing.sh)

vendor-mathlib:
	@$(ECHOOK) "📦 Vendoring mathlib for Lean..."
	$(if $(filter Windows_NT,$(OS)),scripts\vendor-mathlib.bat,sh scripts/vendor-mathlib.sh)
	@$(ECHOOK) "✅ vendor/mathlib ready"

lint:
	@$(ECHOOK) "🔍 Running linting on all code..."
	cd services/spec-service && go fmt ./... && go vet ./...
	cd services/proof-service && go fmt ./... && go vet ./...
	cd services/build-orchestrator && go fmt ./... && go vet ./...
	cd services/evidence-service && go fmt ./... && go vet ./...
	cd services/replay-service && go fmt ./... && go vet ./...
	cd services/api-gateway && go fmt ./... && go vet ./...
	cd runtime/sidecar-watcher && cargo fmt && cargo clippy
	cd console && npm run lint
	cd demos/verifiable-mcp-fraud && npm run lint
	cd core/sdk/typescript && npm run lint
	python -m flake8 tools/ tests/
	@$(ECHOOK) "✅ Linting completed"

bench:
	@$(ECHOOK) "⚡ Running performance benchmarks..."
	cd demos/verifiable-mcp-fraud && npm run benchmark
	python tests/performance/performance_benchmarks.py
	@$(ECHOOK) "✅ Benchmarks completed"

# Save Criterion baseline and record machine/date/SHA in bench/BASELINE.md (see bench/README.md).
bench-save-baseline:
	@$(ECHOOK) "Saving Criterion baseline (provability-fabric-bench)..."
	cargo bench -p provability-fabric-bench -- --save-baseline main
	@python -c "\
import datetime, os, platform, subprocess; \
d = datetime.datetime.now(datetime.timezone.utc).isoformat(); \
sha = subprocess.run(['git','rev-parse','HEAD'], capture_output=True, text=True).stdout.strip() or 'unknown'; \
m = platform.uname(); machine = f'{m.system} {m.release} {m.machine}'; \
p = os.path.join('bench','BASELINE.md'); \
open(p,'w').write(f'Criterion baseline: main\ndate: {d}\ngit_sha: {sha}\nmachine: {machine}\n'); \
print('Wrote', p)"
	@$(ECHOOK) "Baseline saved. See bench/BASELINE.md and target/criterion/"

# ---------- SWE-bench Step-2 (WSL/Linux; see experiments/exp-step2-lite-smoke/commands.md) ----------
# Run from repo root. For swebench-compare and swebench-triage, set BASELINE_RUN_DIR and PF_RUN_DIR
# from experiments/exp-step2-lite-smoke/run-ids.md (e.g. runs/exp-step2-lite-smoke/baseline/<run_id>).
EXP_DIR := runs/exp-step2-lite-smoke
swebench-step2:
	@$(ECHOOK) "Running Step-2 parity cycle (baseline + PF + harness + compare with gates)..."
	$(if $(filter Windows_NT,$(OS)),@$(ECHOOK) "Run in WSL: bash experiments/scripts/run-baseline-pf-cycle.sh" && exit 1,bash experiments/scripts/run-baseline-pf-cycle.sh)
	@$(ECHOOK) "Step-2 cycle done."

swebench-compare:
	@$(if $(and $(BASELINE_RUN_DIR),$(PF_RUN_DIR)),,\
		$(ECHOOK) "Error: set BASELINE_RUN_DIR and PF_RUN_DIR (see run-ids.md). Example:";\
		$(ECHOOK) "  make swebench-compare BASELINE_RUN_DIR=$(EXP_DIR)/baseline/<run_id> PF_RUN_DIR=$(EXP_DIR)/pf/<run_id>";\
		exit 1)
	@$(ECHOOK) "Comparing baseline vs PF with full golden gates (harness, compliance, patch-apply, priced-models)..."
	@python experiments/scripts/compare_runs.py \
		--experiment-dir $(EXP_DIR) \
		--baseline-run-dir $(BASELINE_RUN_DIR) \
		--pf-run-dir $(PF_RUN_DIR) \
		--require-harness --require-compliance --require-patch-apply --require-priced-models
	@$(ECHOOK) "compare.json and compare.csv written to $(EXP_DIR)."

swebench-triage:
	@$(if $(and $(BASELINE_RUN_DIR),$(PF_RUN_DIR)),,\
		$(ECHOOK) "Error: set BASELINE_RUN_DIR and PF_RUN_DIR (see run-ids.md).";\
		exit 1)
	@$(ECHOOK) "Listing delta cases and extracting case bundles..."
	@mkdir -p $(EXP_DIR)/analysis
	@python experiments/scripts/list_delta_cases.py --compare-csv $(EXP_DIR)/compare.csv --out-dir $(EXP_DIR)/analysis
	@python experiments/scripts/extract_case_bundle.py \
		--instance-ids-file $(EXP_DIR)/analysis/baseline_solved_pf_failed.txt \
		--baseline-run-dir $(BASELINE_RUN_DIR) \
		--pf-run-dir $(PF_RUN_DIR) \
		--baseline-eval-dir $(EXP_DIR)/baseline/eval \
		--pf-eval-dir $(EXP_DIR)/pf/eval \
		--out-dir $(EXP_DIR)/analysis/cases || true
	@$(ECHOOK) "Triage done. See $(EXP_DIR)/analysis/"

# Consume baseline_solved_pf_failed.txt: list deltas, extract case bundles, bucket PF failures. Use after a PF regression to prepare fix loop.
swebench-regressions:
	@$(if $(and $(BASELINE_RUN_DIR),$(PF_RUN_DIR)),,\
		$(ECHOOK) "Error: set BASELINE_RUN_DIR and PF_RUN_DIR (see run-ids.md).";\
		exit 1)
	@$(ECHOOK) "Running regression triage (list_delta_cases + extract_case_bundle + bucket)..."
	@mkdir -p $(EXP_DIR)/analysis
	@python experiments/scripts/list_delta_cases.py --compare-csv $(EXP_DIR)/compare.csv --out-dir $(EXP_DIR)/analysis
	@python experiments/scripts/extract_case_bundle.py \
		--instance-ids-file $(EXP_DIR)/analysis/baseline_solved_pf_failed.txt \
		--baseline-run-dir $(BASELINE_RUN_DIR) \
		--pf-run-dir $(PF_RUN_DIR) \
		--baseline-eval-dir $(EXP_DIR)/baseline/eval \
		--pf-eval-dir $(EXP_DIR)/pf/eval \
		--out-dir $(EXP_DIR)/analysis/cases || true
	@python experiments/scripts/bucket_pf_failures_from_cases.py \
		--compare-csv $(EXP_DIR)/compare.csv \
		--cases-dir $(EXP_DIR)/analysis/cases \
		--out-csv $(EXP_DIR)/analysis/pf_failure_buckets.csv 2>/dev/null || true
	@$(ECHOOK) "Regressions: $(EXP_DIR)/analysis/baseline_solved_pf_failed.txt, $(EXP_DIR)/analysis/cases/, $(EXP_DIR)/analysis/pf_failure_buckets.csv. Rerun only regression slice then re-harness + make swebench-compare (includes --require-priced-models)."

security:
	@$(ECHOOK) "🔒 Running security tests..."
	python tests/redteam/abac_fuzz.py --queries 1000
	python tests/redteam/pii_leak.py --vectors 1000
	python tests/security/malicious_adapter_test.py
	@$(ECHOOK) "✅ Security tests completed"

test-all: test security bench validate-certs
	@$(ECHOOK) "🎉 All tests completed successfully!"

# ---------- Deploy helpers ----------
helm-install:
	@$(ECHOOK) "☸️  Installing with Helm..."
	helm install sentinelops-platform charts/pf-enforce/ \
		--set global.environment=production \
		--set global.domain=platform.sentinelops.ai
	@$(ECHOOK) "✅ Helm installation completed"

helm-upgrade:
	@$(ECHOOK) "🔄 Upgrading Helm deployment..."
	helm upgrade sentinelops-platform charts/pf-enforce/
	@$(ECHOOK) "✅ Helm upgrade completed"

# ---------- Docs ----------
docs:
	@$(ECHOOK) "📚 Building documentation..."
	mkdocs build
	@$(ECHOOK) "✅ Documentation built"

docs-serve:
	@$(ECHOOK) "📚 Serving documentation..."
	mkdocs serve --dev-addr=127.0.0.1:8002

# ---------- Placeholder burn-down (P1) ----------
# Fails if forbidden placeholder/stub patterns exist outside allowlisted paths.
# Allowlist: docs/placeholder-burn-down-allowlist.txt
no-runtime-placeholders:
	@$(ECHOOK) "Checking for forbidden placeholder/stub patterns..."
	@python scripts/check_no_placeholder.py || (echo "no-runtime-placeholders: fix or allowlist entries (see docs/placeholder-burn-down.md)" && exit 1)

# ---------- Convenience ----------
logs:
	$(DC) logs -f

rebuild:
	$(DC) build --no-cache
	$(MAKE) demo-up

quick-start: build demo-up
	@$(ECHOOK) ""
	@$(ECHOOK) "🎉 SentinelOps Platform is ready!"
	@$(ECHOOK) ""
	@$(ECHOOK) "👨‍💻 For Developers:"
	@$(ECHOOK) "  Write policy in English → see ActionDSL preview → compile → proof run → deploy"
	@$(ECHOOK) ""
	@$(ECHOOK) "🛡️  For Security/Compliance:"
	@$(ECHOOK) "  Browse certificates → filter by policy/tenant → export compliance packet"
	@$(ECHOOK) ""
	@$(ECHOOK) "⚙️  For SRE/Platform:"
	@$(ECHOOK) "  Monitor SLOs → check cert validation → roll back epochs → fetch artifacts"
