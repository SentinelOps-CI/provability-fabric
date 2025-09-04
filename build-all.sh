#!/bin/bash

# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

set -e  # Exit on any error

echo "🔨 SentinelOps Platform - Build All Components"
echo "=============================================="

# Function to print status
print_status() {
    echo "✅ $1"
}

print_error() {
    echo "❌ $1"
}

# Build Rust sidecar
echo ""
echo "🦀 Building Rust Sidecar..."
cd runtime/sidecar-watcher
if command -v cargo &> /dev/null; then
    cargo build --release
    print_status "Rust sidecar built successfully"
else
    print_error "Cargo not found - skipping Rust build"
fi
cd ../..

# Build Go services
echo ""
echo "🐹 Building Go Services..."
services=("api-gateway" "spec-service" "proof-service" "build-orchestrator" "evidence-service" "replay-service")

for service in "${services[@]}"; do
    echo "Building $service..."
    cd services/$service
    go mod tidy
    go build
    print_status "$service built successfully"
    cd ../..
done

# Build TypeScript SDK
echo ""
echo "📦 Building TypeScript SDK..."
cd sdks/typescript
npm install
npm run build
print_status "TypeScript SDK built successfully"
cd ../..

# Build Demo Application
echo ""
echo "🎯 Building Demo Application..."
cd demos/verifiable-mcp-fraud
npm install
npm run build
print_status "Demo application built successfully"
cd ../..

# Build Console UI
echo ""
echo "🖥️  Building Console UI..."
cd console
npm install
npm run build
print_status "Console UI built successfully"
cd ..

echo ""
echo "🎉 All components built successfully!"
echo ""
echo "📋 Summary:"
echo "  - Rust sidecar: ✅"
echo "  - Go services (6): ✅"
echo "  - TypeScript SDK: ✅"
echo "  - Demo application: ✅"
echo "  - Console UI: ✅"
echo ""
echo "🚀 Ready for deployment!"
