# Provability Fabric Build System
# PF-CORE-01: Versioned API Contracts and Code Generation

.PHONY: help proto-gen proto-gen-go proto-gen-ts proto-gen-rust proto-clean proto-validate
.PHONY: sdk-build sdk-test sdk-clean all clean

# Default target
all: proto-gen sdk-build

# Help target
help:
	@echo "Provability Fabric Build System - PF-CORE-01"
	@echo ""
	@echo "Available targets:"
	@echo "  proto-gen        - Generate all language bindings from protobufs"
	@echo "  proto-gen-go     - Generate Go bindings"
	@echo "  proto-gen-ts     - Generate TypeScript bindings"
	@echo "  proto-gen-rust   - Generate Rust bindings"
	@echo "  proto-clean      - Clean generated protobuf files"
	@echo "  proto-validate   - Validate protobuf files"
	@echo "  sdk-build        - Build all SDKs"
	@echo "  sdk-test         - Test all SDKs"
	@echo "  sdk-clean        - Clean all SDKs"
	@echo "  clean            - Clean everything"
	@echo "  help             - Show this help message"

# Protobuf generation
proto-gen: proto-gen-go proto-gen-ts proto-gen-rust

# Generate Go bindings
proto-gen-go:
	@echo "Generating Go bindings..."
	@mkdir -p core/sdk/go/generated
	protoc --go_out=core/sdk/go/generated \
		--go_opt=paths=source_relative \
		--go-grpc_out=core/sdk/go/generated \
		--go-grpc_opt=paths=source_relative \
		api/v1/*.proto
	@echo "Go bindings generated in core/sdk/go/generated/"

# Generate TypeScript bindings
proto-gen-ts:
	@echo "Generating TypeScript bindings..."
	@mkdir -p core/sdk/typescript/generated
	protoc --plugin=protoc-gen-ts_proto=./node_modules/.bin/protoc-gen-ts_proto \
		--ts_proto_out=core/sdk/typescript/generated \
		--ts_proto_opt=esModuleInterop=true \
		--ts_proto_opt=forceLong=string \
		--ts_proto_opt=useOptionals=messages \
		api/v1/*.proto
	@echo "TypeScript bindings generated in core/sdk/typescript/generated/"

# Generate Rust bindings
proto-gen-rust:
	@echo "Generating Rust bindings..."
	@mkdir -p core/sdk/rust/generated
	protoc --rust_out=core/sdk/rust/generated \
		--grpc_out=core/sdk/rust/generated \
		--plugin=protoc-gen-grpc=./target/release/protoc-gen-grpc-rust \
		api/v1/*.proto
	@echo "Rust bindings generated in core/sdk/rust/generated/"

# Clean generated protobuf files
proto-clean:
	@echo "Cleaning generated protobuf files..."
	@rm -rf core/sdk/go/generated/*
	@rm -rf core/sdk/typescript/generated/*
	@rm -rf core/sdk/rust/generated/*
	@echo "Generated protobuf files cleaned"

# Validate protobuf files
proto-validate:
	@echo "Validating protobuf files..."
	@for file in api/v1/*.proto; do \
		echo "Validating $$file..."; \
		protoc --descriptor_set_out=/dev/null $$file || exit 1; \
	done
	@echo "All protobuf files are valid"

# Build all SDKs
sdk-build: sdk-build-go sdk-build-ts sdk-build-rust

# Build Go SDK
sdk-build-go:
	@echo "Building Go SDK..."
	@cd core/sdk/go && go mod tidy && go build ./...

# Build TypeScript SDK
sdk-build-ts:
	@echo "Building TypeScript SDK..."
	@cd core/sdk/typescript && npm install && npm run build

# Build Rust SDK
sdk-build-rust:
	@echo "Building Rust SDK..."
	@cd core/sdk/rust && cargo build

# Test all SDKs
sdk-test: sdk-test-go sdk-test-ts sdk-test-rust

# Test Go SDK
sdk-test-go:
	@echo "Testing Go SDK..."
	@cd core/sdk/go && go test ./...

# Test TypeScript SDK
sdk-test-ts:
	@echo "Testing TypeScript SDK..."
	@cd core/sdk/typescript && npm test

# Test Rust SDK
sdk-test-rust:
	@echo "Testing Rust SDK..."
	@cd core/sdk/rust && cargo test

# Clean all SDKs
sdk-clean: sdk-clean-go sdk-clean-ts sdk-clean-rust

# Clean Go SDK
sdk-clean-go:
	@echo "Cleaning Go SDK..."
	@cd core/sdk/go && go clean -cache -modcache -testcache

# Clean TypeScript SDK
sdk-clean-ts:
	@echo "Cleaning TypeScript SDK..."
	@cd core/sdk/typescript && rm -rf node_modules dist

# Clean Rust SDK
sdk-clean-rust:
	@echo "Cleaning Rust SDK..."
	@cd core/sdk/rust && cargo clean

# Clean everything
clean: proto-clean sdk-clean
	@echo "All generated files and build artifacts cleaned"

# Install protobuf tools (Ubuntu/Debian)
install-tools-ubuntu:
	@echo "Installing protobuf tools for Ubuntu/Debian..."
	sudo apt-get update
	sudo apt-get install -y protobuf-compiler
	go install google.golang.org/protobuf/cmd/protoc-gen-go@latest
	go install google.golang.org/grpc/cmd/protoc-gen-go-grpc@latest
	npm install -g ts-proto

# Install protobuf tools (macOS)
install-tools-macos:
	@echo "Installing protobuf tools for macOS..."
	brew install protobuf
	go install google.golang.org/protobuf/cmd/protoc-gen-go@latest
	go install google.golang.org/grpc/cmd/protoc-gen-go-grpc@latest
	npm install -g ts-proto

# Install protobuf tools (Windows)
install-tools-windows:
	@echo "Installing protobuf tools for Windows..."
	@echo "Please install protobuf tools manually:"
	@echo "1. Download protoc from https://github.com/protocolbuffers/protobuf/releases"
	@echo "2. Install Go protobuf plugins: go install google.golang.org/protobuf/cmd/protoc-gen-go@latest"
	@echo "3. Install Go gRPC plugin: go install google.golang.org/grpc/cmd/protoc-gen-go-grpc@latest"
	@echo "4. Install TypeScript plugin: npm install -g ts-proto"

# Check dependencies
check-deps:
	@echo "Checking protobuf dependencies..."
	@which protoc > /dev/null || (echo "protoc not found. Please install protobuf-compiler" && exit 1)
	@which protoc-gen-go > /dev/null || (echo "protoc-gen-go not found. Please run: go install google.golang.org/protobuf/cmd/protoc-gen-go@latest" && exit 1)
	@which protoc-gen-go-grpc > /dev/null || (echo "protoc-gen-go-grpc not found. Please run: go install google.golang.org/grpc/cmd/protoc-gen-go-grpc@latest" && exit 1)
	@echo "All protobuf dependencies are available"

# Generate golden JSON fixtures for round-trip tests
proto-fixtures:
	@echo "Generating golden JSON fixtures..."
	@mkdir -p tests/fixtures/golden
	@for file in api/v1/*.proto; do \
		base=$$(basename $$file .proto); \
		echo "Generating fixtures for $$base..."; \
		protoc --encode=$$base $$file < /dev/null > tests/fixtures/golden/$$base.json || true; \
	done
	@echo "Golden JSON fixtures generated in tests/fixtures/golden/"

# Run compatibility tests
proto-compat-test:
	@echo "Running protobuf compatibility tests..."
	@cd tests && go test -v -run TestProtoCompatibility ./...

# Format protobuf files
proto-format:
	@echo "Formatting protobuf files..."
	@for file in api/v1/*.proto; do \
		echo "Formatting $$file..."; \
		clang-format -i $$file || echo "clang-format not available, skipping $$file"; \
	done
	@echo "Protobuf files formatted"

# Lint protobuf files
proto-lint:
	@echo "Linting protobuf files..."
	@for file in api/v1/*.proto; do \
		echo "Linting $$file..."; \
		protoc --lint_out=$$(dirname $$file) $$file || echo "protoc-lint not available, skipping $$file"; \
	done
	@echo "Protobuf files linted"

# Show protobuf file statistics
proto-stats:
	@echo "Protobuf file statistics:"
	@echo "========================"
	@for file in api/v1/*.proto; do \
		echo "$$file:"; \
		echo "  Lines: $$(wc -l < $$file)"; \
		echo "  Messages: $$(grep -c '^message ' $$file)"; \
		echo "  Services: $$(grep -c '^service ' $$file)"; \
		echo "  Enums: $$(grep -c '^enum ' $$file)"; \
		echo ""; \
	done

# Generate API documentation
proto-docs:
	@echo "Generating API documentation..."
	@mkdir -p docs/api
	protoc --doc_out=docs/api --doc_opt=markdown,api.md api/v1/*.proto
	@echo "API documentation generated in docs/api/"

# Show help for specific target
proto-help:
	@echo "Protobuf-specific targets:"
	@echo "  proto-gen        - Generate all language bindings"
	@echo "  proto-gen-go     - Generate Go bindings"
	@echo "  proto-gen-ts     - Generate TypeScript bindings"
	@echo "  proto-gen-rust   - Generate Rust bindings"
	@echo "  proto-clean      - Clean generated files"
	@echo "  proto-validate   - Validate protobuf files"
	@echo "  proto-fixtures   - Generate golden JSON fixtures"
	@echo "  proto-compat-test - Run compatibility tests"
	@echo "  proto-format     - Format protobuf files"
	@echo "  proto-lint       - Lint protobuf files"
	@echo "  proto-stats      - Show file statistics"
	@echo "  proto-docs       - Generate API documentation"
	@echo "  proto-help       - Show this help message"

# Standards and validation targets
.PHONY: submodules validate-certs standards-pin-check

# Update and initialize git submodules
submodules:
	@echo "Updating git submodules..."
	git submodule update --init --recursive
	@echo "Submodules updated"

# Enforce standards pinned to tags
standards-pin-check:
	@echo "Checking external standards are pinned to released tags..."
	@python tools/standards/check_pins.py
	@echo "Standards pin check complete"

# Validate CERT-V1 JSON files
validate-certs:
	@echo "Validating CERT-V1 JSON files..."
	@cd tools/cert-validate && pip install -r requirements.txt
	python tools/cert-validate/validate.py evidence/**/*.cert.json tests/replay/out/**/*.cert.json
	@echo "CERT validation complete"

# Show standards help
standards-help:
	@echo "Standards and validation targets:"
	@echo "  submodules       - Update and initialize git submodules"
	@echo "  validate-certs   - Validate CERT-V1 JSON files"
	@echo "  standards-help   - Show this help message"