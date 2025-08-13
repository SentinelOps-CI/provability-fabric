#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -e

# Publish script for TypeScript SDK
echo "🚀 Publishing TypeScript SDK to npm..."

# Check if we're in the right directory
if [ ! -f "package.json" ]; then
    echo "❌ Error: package.json not found. Run this script from the typescript SDK directory."
    exit 1
fi

# Check if npm is available
if ! command -v npm &> /dev/null; then
    echo "❌ Error: npm is not installed or not in PATH"
    exit 1
fi

# Check if user is logged in to npm
if ! npm whoami &> /dev/null; then
    echo "❌ Error: Not logged in to npm. Run 'npm login' first."
    exit 1
fi

# Clean previous builds
echo "🧹 Cleaning previous builds..."
rm -rf dist/ node_modules/ package-lock.json

# Install dependencies
echo "📦 Installing dependencies..."
npm install

# Run tests
echo "🧪 Running tests..."
npm test

# Build the package
echo "🔨 Building package..."
npm run build

# Check if build was successful
if [ ! -d "dist" ]; then
    echo "❌ Error: Build failed - dist directory not found"
    exit 1
fi

# Run linting
echo "🔍 Running linting..."
npm run lint

# Check package size
echo "📏 Checking package size..."
npm run size

# Prompt for confirmation
read -p "🤔 Ready to publish version $(node -p "require('./package.json').version")? (y/N): " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "❌ Publishing cancelled"
    exit 1
fi

# Publish to npm
echo "📤 Publishing to npm..."
npm publish --access public

echo "✅ Successfully published TypeScript SDK to npm!"
echo "📦 Package: @provability-fabric/core-sdk-typescript"
echo "🔗 URL: https://www.npmjs.com/package/@provability-fabric/core-sdk-typescript"
