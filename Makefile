# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

.PHONY: help build test clean demo-up demo-down demo-setup install dev validate-certs lint bench security test-all helm-install helm-upgrade docs docs-serve quick-start logs rebuild

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
	@$(ECHOOK) "  make install         - Install platform locally"
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
install:
	@$(ECHOOK) "📦 Installing SentinelOps Platform locally..."
	./scripts/install.sh
	@$(ECHOOK) "✅ Platform installed successfully"

validate-certs:
	@$(ECHOOK) "🔍 Validating CERT-V1 certificates..."
	python tools/cert-validate/validate.py evidence/egress_certs/*.json
	python tools/cert-validate/validate.py evidence/certs/**/*.cert.json
	@$(ECHOOK) "✅ Certificate validation completed"

lint:
	@$(ECHOOK) "🔍 Running linting on all code..."
	# Go services
	cd services/spec-service && go fmt ./... && go vet ./...
	cd services/proof-service && go fmt ./... && go vet ./...
	cd services/build-orchestrator && go fmt ./... && go vet ./...
	cd services/evidence-service && go fmt ./... && go vet ./...
	cd services/replay-service && go fmt ./... && go vet ./...
	cd services/api-gateway && go fmt ./... && go vet ./...
	# Rust sidecar
	cd runtime/sidecar-watcher && cargo fmt && cargo clippy
	# TypeScript
	cd console && npm run lint
	cd demos/verifiable-mcp-fraud && npm run lint
	cd core/sdk/typescript && npm run lint
	# Python
	python -m flake8 tools/ tests/ --max-line-length=100
	@$(ECHOOK) "✅ Linting completed"

bench:
	@$(ECHOOK) "⚡ Running performance benchmarks..."
	cd demos/verifiable-mcp-fraud && npm run benchmark
	python tests/performance/performance_benchmarks.py
	@$(ECHOOK) "✅ Benchmarks completed"

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
