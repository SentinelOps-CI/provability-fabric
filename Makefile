# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

.PHONY: help build test clean demo-up demo-down install dev

# Default target
help:
	@echo "SentinelOps Platform - Available Commands:"
	@echo ""
	@echo "Development:"
	@echo "  make dev          - Start development environment"
	@echo "  make build        - Build all services"
	@echo "  make test         - Run all tests"
	@echo "  make clean        - Clean build artifacts"
	@echo ""
	@echo "Demo:"
	@echo "  make demo-up      - Start complete demo environment"
	@echo "  make demo-down    - Stop demo environment"
	@echo "  make demo-setup   - Setup demo data and policies"
	@echo ""
	@echo "Platform:"
	@echo "  make install      - Install platform locally"
	@echo "  make validate-certs - Validate all CERT-V1 certificates"
	@echo "  make lint         - Run linting on all code"
	@echo ""

# Development environment
dev:
	@echo "🚀 Starting SentinelOps Platform development environment..."
	docker-compose up --build -d postgres redis
	@echo "⏳ Waiting for databases to be ready..."
	sleep 10
	@echo "🔧 Starting platform services..."
	docker-compose up --build api-gateway spec-service proof-service build-orchestrator evidence-service replay-service runtime-sidecar
	@echo "✅ Development environment ready!"
	@echo "🌐 Console UI: http://localhost:3000"
	@echo "🔗 API Gateway: http://localhost:8000"

# Build all services
build:
	@echo "🔨 Building all platform services..."
	docker-compose build

# Run tests
test:
	@echo "🧪 Running platform tests..."
	python tests/trust_fire_orchestrator.py
	@echo "🧪 Running integration tests..."
	python tests/integration/test_platform_integration.py
	@echo "🧪 Running demo tests..."
	cd demos/verifiable-mcp-fraud && npm test

# Clean build artifacts
clean:
	@echo "🧹 Cleaning build artifacts..."
	docker-compose down -v
	docker system prune -f
	rm -rf build/ dist/ coverage/ .pytest_cache/
	find . -name "*.pyc" -delete
	find . -name "__pycache__" -delete

# Demo environment
demo-up:
	@echo "🎬 Starting SentinelOps Platform Demo..."
	@echo "📋 This will start the complete platform with the Verifiable MCP Fraud demo"
	docker-compose up --build -d
	@echo "⏳ Waiting for services to be ready..."
	sleep 30
	@echo "🎯 Setting up demo data..."
	$(MAKE) demo-setup
	@echo ""
	@echo "✅ Demo environment ready!"
	@echo ""
	@echo "🌐 Access Points:"
	@echo "  Console UI:     http://localhost:3000"
	@echo "  API Gateway:    http://localhost:8000"
	@echo "  Grafana:        http://localhost:3002 (admin/admin)"
	@echo "  Demo App:       http://localhost:3001"
	@echo ""
	@echo "🎯 Demo Flow:"
	@echo "  1. Open Console UI and go to Policies tab"
	@echo "  2. See the fraud detection policy compiled and deployed"
	@echo "  3. Go to Runtime tab to monitor live metrics"
	@echo "  4. Go to Evidence tab to see CERT-V1 certificates"
	@echo "  5. Run replays to verify 99.9%+ low-view equality"
	@echo "  6. Download compliance packets"

demo-down:
	@echo "🛑 Stopping demo environment..."
	docker-compose down
	@echo "✅ Demo environment stopped"

demo-setup:
	@echo "🎯 Setting up demo data and policies..."
	cd demos/verifiable-mcp-fraud && npm run demo:setup
	@echo "✅ Demo setup completed"

# Install platform locally
install:
	@echo "📦 Installing SentinelOps Platform locally..."
	./scripts/install.sh
	@echo "✅ Platform installed successfully"

# Validate CERT-V1 certificates
validate-certs:
	@echo "🔍 Validating CERT-V1 certificates..."
	python tools/cert-validate/validate.py evidence/egress_certs/*.json
	python tools/cert-validate/validate.py evidence/certs/**/*.cert.json
	@echo "✅ Certificate validation completed"

# Lint all code
lint:
	@echo "🔍 Running linting on all code..."
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
	cd sdks/typescript && npm run lint
	# Python
	python -m flake8 tools/ tests/ --max-line-length=100
	@echo "✅ Linting completed"

# Performance benchmarks
bench:
	@echo "⚡ Running performance benchmarks..."
	cd demos/verifiable-mcp-fraud && npm run benchmark
	python tests/performance/performance_benchmarks.py
	@echo "✅ Benchmarks completed"

# Security tests
security:
	@echo "🔒 Running security tests..."
	python tests/redteam/abac_fuzz.py --queries 1000
	python tests/redteam/pii_leak.py --vectors 1000
	python tests/security/malicious_adapter_test.py
	@echo "✅ Security tests completed"

# Full test suite
test-all: test security bench validate-certs
	@echo "🎉 All tests completed successfully!"

# Production deployment helpers
helm-install:
	@echo "☸️  Installing with Helm..."
	helm install sentinelops-platform charts/pf-enforce/ \
		--set global.environment=production \
		--set global.domain=platform.sentinelops.ai
	@echo "✅ Helm installation completed"

helm-upgrade:
	@echo "🔄 Upgrading Helm deployment..."
	helm upgrade sentinelops-platform charts/pf-enforce/
	@echo "✅ Helm upgrade completed"

# Documentation
docs:
	@echo "📚 Building documentation..."
	mkdocs build
	@echo "✅ Documentation built"

docs-serve:
	@echo "📚 Serving documentation..."
	mkdocs serve --dev-addr=127.0.0.1:8002

# Quick start for new users
quick-start: build demo-up
	@echo ""
	@echo "🎉 SentinelOps Platform is ready!"
	@echo ""
	@echo "👨‍💻 For Developers:"
	@echo "  Write policy in English → see ActionDSL preview → compile → proof run → deploy"
	@echo ""
	@echo "🛡️  For Security/Compliance:"
	@echo "  Browse certificates → filter by policy/tenant → export compliance packet"
	@echo ""
	@echo "⚙️  For SRE/Platform:"
	@echo "  Monitor SLOs → check cert validation → roll back epochs → fetch artifacts"
	@echo ""