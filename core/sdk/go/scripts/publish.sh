#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -e

# Publish script for Go SDK
echo "🚀 Publishing Go SDK to Go modules..."

# Check if we're in the right directory
if [ ! -f "go.mod" ]; then
    echo "❌ Error: go.mod not found. Run this script from the go SDK directory."
    exit 1
fi

# Check if Go is available
if ! command -v go &> /dev/null; then
    echo "❌ Error: Go is not installed or not in PATH"
    exit 1
fi

# Check Go version
GO_VERSION=$(go version | awk '{print $3}' | sed 's/go//')
echo "🔍 Go version: $GO_VERSION"

# Clean previous builds
echo "🧹 Cleaning previous builds..."
go clean -cache -modcache -testcache
rm -rf go.sum

# Download dependencies
echo "📦 Downloading dependencies..."
go mod download

# Verify dependencies
echo "🔍 Verifying dependencies..."
go mod verify

# Run tests
echo "🧪 Running tests..."
go test -v ./...

# Run benchmarks
echo "📊 Running benchmarks..."
go test -bench=. -benchmem ./...

# Check for race conditions
echo "🏃 Checking for race conditions..."
go test -race ./...

# Build the package
echo "🔨 Building package..."
go build -v .

# Check if build was successful
if [ ! -f "sdk" ]; then
    echo "❌ Error: Build failed - binary not found"
    exit 1
fi

# Run static analysis
echo "🔍 Running static analysis..."
go vet ./...
golangci-lint run ./... 2>/dev/null || echo "⚠️  golangci-lint not available, skipping"

# Check module info
echo "📋 Module information:"
go list -m -json all | jq -r '.Path + " " + .Version' 2>/dev/null || echo "⚠️  jq not available, showing raw output:"
go list -m all

# Prompt for confirmation
VERSION=$(go list -m -f '{{.Version}}' .)
echo "🤔 Ready to publish version $VERSION? (y/N): "
read -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "❌ Publishing cancelled"
    exit 1
fi

# Tag the release
echo "🏷️  Creating git tag..."
git tag -a "v$VERSION" -m "Release version $VERSION"
git push origin "v$VERSION"

echo "✅ Successfully published Go SDK!"
echo "📦 Module: github.com/provability-fabric/core/sdk/go"
echo "🏷️  Version: $VERSION"
echo "🔗 URL: https://pkg.go.dev/github.com/provability-fabric/core/sdk/go"
echo ""
echo "💡 To use the SDK in other projects:"
echo "   go get github.com/provability-fabric/core/sdk/go@v$VERSION"
