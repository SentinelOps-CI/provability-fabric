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

.PHONY: help build test clean demo-up demo-down demo-setup install dev validate-certs lint bench security test-all helm-install helm-upgrade docs docs-strict docs-serve quick-start logs rebuild lean-check-duplicates lean-forbid-shadowing vendor-mathlib no-runtime-placeholders submodules standards-pin-check dev-standards evidence-verify proto-lint proto-validate proto-gen proto-gen-go proto-gen-ts proto-gen-rust proto-fixtures proto-compat-test proto-docs

include scripts/proto.mk

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

# PCS CLI from repo root (Go 1.20+ -C); or use ./pf / pf.cmd
PF ?= go -C core/cli/pf run .

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
	@$(ECHOOK) "  make submodules      - Init/update external standards submodules"
	@$(ECHOOK) "  make standards-pin-check - Verify submodule tags match versions.json"
	@$(ECHOOK) "  make dev-standards   - submodules + standards-pin-check"
	@$(ECHOOK) "  make evidence-verify - Evidence v0.1/v0.2 local gate (Linux/WSL/Git Bash)"
	@$(ECHOOK) "  make lint            - Run linting on all code"
	@$(ECHOOK) ""

# ---------- External standards submodules ----------
submodules:
	@$(ECHOOK) "Initializing external standards submodules..."
	bash scripts/init_external_standards.sh
	@$(ECHOOK) "Submodules ready (run make standards-pin-check to verify tags)"

standards-pin-check:
	@$(ECHOOK) "Checking external standards pin drift..."
	python tools/standards/check_pins.py

dev-standards: submodules standards-pin-check
	@$(ECHOOK) "External standards ready for local development"

evidence-verify: dev-standards
	@$(ECHOOK) "Running Evidence v0.1/v0.2 verification..."
	cd core/evidence && go test ./...
	pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay \
		tests/evidence_trace tests/runtime_evidence tests/testbed -q
	bash testbed/evidence-v0.1/run_happy_path.sh
	bash testbed/evidence-v0.2/run_deep_replay.sh
	@$(ECHOOK) "Evidence verification passed"

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
	@$(ECHOOK) "OK: PCS unit and CLI tests passed"

ifeq ($(OS),Windows_NT)
test-pcs-benchmark:
	@$(ECHOOK) "PCS admission benchmarks..."
	@bash scripts/pcs-benchmark-admission.sh || powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-benchmark-admission.ps1
else
test-pcs-benchmark:
	@$(ECHOOK) "PCS admission benchmarks..."
	@bash scripts/pcs-benchmark-admission.sh
endif

validate-pcs-benchmark-bundle:
	@$(ECHOOK) "Validate PCS admission benchmark bundle (labtrust)..."
	bash scripts/pcs-validate-benchmark-bundle.sh benchmark_runs/labtrust_admission

export-pcs-benchmark-ingest-reference:
	@$(ECHOOK) "Materialize labtrust PcsBenchIngest reference artifact..."
	bash scripts/export-pcs-benchmark-ingest-reference.sh

validate-pcs-reference-ingest:
	@$(ECHOOK) "Validate committed labtrust reference ingest (producer contract)..."
	bash scripts/pcs-validate-reference-ingest.sh

pcs-release-gate:
	@$(ECHOOK) "Syncing PCS schemas from pcs-core..."
	bash scripts/pcs-schema-sync.sh $(PCS_CORE_PATH)
	@$(MAKE) validate-pcs-schema-diff test-pcs-full demo-pcs demo-pcs-release pcs-v01-pf-chain
	@$(ECHOOK) "OK: PCS release gate passed (schemas, full CI gate, demos, PF clean-chain)"

ifeq ($(OS),Windows_NT)
pcs-bench-producer:
	@$(ECHOOK) "PCS-bench producer gate (labtrust admission ingest)..."
	@bash scripts/pcs-bench-producer.sh || powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-bench-producer.ps1
else
pcs-bench-producer:
	@$(ECHOOK) "PCS-bench producer gate (labtrust admission ingest)..."
	@bash scripts/pcs-bench-producer.sh
endif

test-pcs-full: test-pcs test-pcs-rc-gate test-pcs-phase2 validate-pcs-fixtures test-pcs-benchmark validate-pcs-benchmark-bundle pcs-bench-producer validate-pcs-reference-ingest
	@$(ECHOOK) "OK: PCS full gate passed (unit, RC lock, Phase 2, fixtures, admission benchmarks)"

validate-pcs-fixtures:
	@$(ECHOOK) "Validating PCS fixtures..."
	cd tools/pcs-validate && go run . --fixtures ../../tests/pcs

sync-pcs-rc-fixtures:
	@$(ECHOOK) "Syncing PF labtrust-release fixtures from pcs-core RC..."
	python scripts/pcs-sync-from-pcs-core-rc.py $(PCS_CORE_PATH)

sync-pcs-computation-fixtures:
	@$(ECHOOK) "Syncing PF computation-release fixtures from pcs-core..."
	python scripts/pcs-sync-computation-release.py $(PCS_CORE_PATH)

ifeq ($(OS),Windows_NT)
test-pcs-rc-gate:
	@$(ECHOOK) "PCS RC fixture lock tests..."
	powershell -NoProfile -ExecutionPolicy Bypass -File scripts/test-pcs-rc-gate.ps1

test-pcs-phase2:
	@$(ECHOOK) "PCS Phase 2 protocol tests..."
	cd adapters/pcs && go test -count=1 -run "TestPFAcceptsValidHandoffManifest|TestPFEmitsReleaseChainValidationResult|TestReleaseChainResultStatusProofCheckedOnValidChain|TestPFHashMatchesPCSCoreSignedBundleVector|TestPFRejectsIllegalStatusTransition|TestReleaseModeRejectsLegacyPFHandoff|TestReleaseModeRequiresHandoffManifest|TestReleaseModeRequiresArtifactRegistry|TestRegistryWrongProducerRejected|TestRegistryDisallowedStatusRejected|TestRegistryMissingRequiredFieldRejected|TestReleaseChainResultContainsRegistryChecks|TestPFExplainFailureContainsRepairCommand|TestPFExplainReleaseChainContainsRepairCommand|TestLocalDevStillAcceptsLegacyHandoffWithWarning" ./...
else
test-pcs-rc-gate:
	@$(ECHOOK) "PCS RC fixture lock tests..."
	bash scripts/test-pcs-rc-gate.sh

test-pcs-phase2:
	@$(ECHOOK) "PCS Phase 2 protocol tests..."
	cd adapters/pcs && go test -count=1 -run 'TestPFAcceptsValidHandoffManifest|TestPFEmitsReleaseChainValidationResult|TestReleaseChainResultStatusProofCheckedOnValidChain|TestPFHashMatchesPCSCoreSignedBundleVector|TestPFRejectsIllegalStatusTransition|TestReleaseModeRejectsLegacyPFHandoff|TestReleaseModeRequiresHandoffManifest|TestReleaseModeRequiresArtifactRegistry|TestRegistryWrongProducerRejected|TestRegistryDisallowedStatusRejected|TestRegistryMissingRequiredFieldRejected|TestReleaseChainResultContainsRegistryChecks|TestPFExplainFailureContainsRepairCommand|TestPFExplainReleaseChainContainsRepairCommand|TestLocalDevStillAcceptsLegacyHandoffWithWarning' ./...
endif

ifeq ($(OS),Windows_NT)
freeze-pcs-labtrust-signed:
	@$(ECHOOK) "Regenerating PF-signed LabTrust fixture..."
	powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-freeze-labtrust-signed.ps1

freeze-pcs-labtrust-release:
	@$(ECHOOK) "Freezing LabTrust-CertifyEdge release fixtures..."
	powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-freeze-labtrust-release.ps1

pcs-v01-pf-chain:
	@$(ECHOOK) "PCS v0.1 PF clean-chain segment (release-run/, does not mutate fixtures)..."
	@powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-pf-clean-chain.ps1 release-run
else
freeze-pcs-labtrust-signed:
	@$(ECHOOK) "Regenerating PF-signed LabTrust fixture..."
	bash scripts/pcs-freeze-labtrust-signed.sh

freeze-pcs-labtrust-release:
	@$(ECHOOK) "Freezing LabTrust-CertifyEdge release fixtures..."
	bash scripts/pcs-freeze-labtrust-release.sh

pcs-v01-pf-chain:
	@$(ECHOOK) "PCS v0.1 PF clean-chain segment (release-run/, does not mutate fixtures)..."
	@PF_RELEASE_MODE=1 PF="$(PF)" bash scripts/pcs-pf-clean-chain.sh release-run
endif

pcs-v01-clean-chain:
	@$(ECHOOK) "PCS v0.1 full clean-checkout chain..."
	bash scripts/run-pcs-v01-clean-chain.sh

demo-pcs-release:
	@$(ECHOOK) "PCS LabTrust release verify / sign / inspect / validate..."
	$(PF) verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json
	$(PF) validate verification-result tests/pcs/fixtures/labtrust-release/verification_result.json
	$(PF) validate signed-science-claim tests/pcs/fixtures/labtrust-release/signed_science_claim_bundle.json
	$(PF) inspect science-claim tests/pcs/fixtures/labtrust-release/signed_science_claim_bundle.json --strict

validate-pcs-schema-diff:
	@$(ECHOOK) "Comparing config/schemas/pcs to pcs-core..."
	bash scripts/pcs-schema-diff.sh $(PCS_CORE_PATH)

sync-pcs-schemas:
	@$(ECHOOK) "Syncing PCS schemas from pcs-core..."
	bash scripts/pcs-schema-sync.sh $(PCS_CORE_PATH)

demo-pcs:
	@$(ECHOOK) "PCS verify / sign / inspect demo (run from repo root)..."
	$(PF) verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
	$(PF) sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json --out tests/pcs/signed_science_claim_bundle.demo.json
	$(PF) inspect science-claim tests/pcs/signed_science_claim_bundle.demo.json --strict
	$(PF) inspect science-claim tests/pcs/fixtures/labtrust/signed_science_claim_bundle.labtrust-export.json --reverify
	@$(ECHOOK) "OK: PCS demo completed (verify, sign, inspect --strict, inspect --reverify)"

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
	@if [ ! -f external/CERT-V1/schema/cert-v1.schema.json ]; then \
		echo "CERT-V1 schema missing at external/CERT-V1/schema/cert-v1.schema.json"; \
		echo "Clone per external/README.md or pass --allow-missing-schema (not recommended)."; \
		exit 1; \
	fi
	@set -e; shopt -s nullglob; files=(evidence/certs/*/*.cert.json tests/replay/out/**/*.cert.json); \
	if [ $${#files[@]} -eq 0 ]; then \
		echo "No CERT-V1 *.cert.json fixtures found (egress_certs/ uses a separate schema)."; \
	else \
		python tools/cert-validate/validate.py "$${files[@]}"; \
	fi
	@$(ECHOOK) "✅ Certificate validation completed"

lean-check-duplicates:
	@$(ECHOOK) "🔍 Checking for duplicate Lean definitions..."
	python tools/lean_ast_hash.py .

lean-forbid-shadowing:
	@$(ECHOOK) "🔍 Checking for forbidden shadowing..."
	$(if $(filter Windows_NT,$(OS)),@$(ECHOOK) "Skipped on Windows (run scripts/forbid-shadowing.sh in Git Bash)" && exit 0,bash scripts/forbid-shadowing.sh)

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

docs-strict:
	@$(ECHOOK) "📚 Building documentation (strict)..."
	mkdocs build --strict
	@$(ECHOOK) "✅ Strict documentation build passed"

docs-serve:
	@$(ECHOOK) "📚 Serving documentation..."
	mkdocs serve --dev-addr=127.0.0.1:8002

# ---------- Placeholder burn-down (P1) ----------
# Fails if forbidden placeholder/stub patterns exist outside allowlisted paths.
# Allowlist: docs/internal/placeholders/placeholder-burn-down-allowlist.txt
no-runtime-placeholders:
	@$(ECHOOK) "Checking for forbidden placeholder/stub patterns..."
	@python scripts/check_no_placeholder.py || (echo "no-runtime-placeholders: fix or allowlist entries (see docs/internal/placeholders/placeholder-burn-down-allowlist.txt)" && exit 1)

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
