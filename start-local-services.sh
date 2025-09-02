#!/bin/bash

# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

# Start SentinelOps Platform services locally

set -e

echo "🚀 Starting SentinelOps Platform services locally..."

# Set common environment variables
export DATABASE_URL="postgres://sentinelops:sentinelops_password@localhost:5432/sentinelops"
export REDIS_URL="redis://localhost:6379"
export GIN_MODE=release

# Start services in background
echo "📋 Starting Spec Service (port 8001)..."
cd services/spec-service && go run main.go &
SPEC_PID=$!

echo "🔍 Starting Proof Service (port 8002)..."
cd ../proof-service && go run main.go &
PROOF_PID=$!

echo "🏗️ Starting Build Orchestrator (port 8003)..."
cd ../build-orchestrator && go run main.go &
BUILD_PID=$!

echo "📊 Starting Evidence Service (port 8004)..."
cd ../evidence-service && go run main.go &
EVIDENCE_PID=$!

echo "🔄 Starting Replay Service (port 8005)..."
cd ../replay-service && go run main.go &
REPLAY_PID=$!

echo "🛡️ Starting API Gateway (port 8000)..."
cd ../api-gateway && go run main.go &
GATEWAY_PID=$!

cd ../..

echo "⏳ Waiting for services to start..."
sleep 10

echo "✅ Services started! PIDs:"
echo "  Spec Service: $SPEC_PID"
echo "  Proof Service: $PROOF_PID" 
echo "  Build Orchestrator: $BUILD_PID"
echo "  Evidence Service: $EVIDENCE_PID"
echo "  Replay Service: $REPLAY_PID"
echo "  API Gateway: $GATEWAY_PID"

echo ""
echo "🌐 Platform URLs:"
echo "  API Gateway: http://localhost:8000"
echo "  Health Check: http://localhost:8000/health"

# Keep script running
echo ""
echo "Press Ctrl+C to stop all services..."
wait