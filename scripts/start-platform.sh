#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

set -e

echo "🚀 Starting SentinelOps Platform"
echo "=================================="

# Check prerequisites
echo "🔍 Checking prerequisites..."

if ! command -v docker &> /dev/null; then
    echo "❌ Docker is required but not installed"
    exit 1
fi

if ! command -v docker-compose &> /dev/null; then
    echo "❌ Docker Compose is required but not installed"
    exit 1
fi

echo "✅ Prerequisites satisfied"

# Start platform
echo ""
echo "🔧 Starting platform services..."
docker-compose up --build -d

echo ""
echo "⏳ Waiting for services to be ready..."
sleep 30

# Health checks
echo ""
echo "🏥 Performing health checks..."

services=("api-gateway:8000" "spec-service:8001" "proof-service:8002" "build-orchestrator:8003" "evidence-service:8004" "replay-service:8005")

for service in "${services[@]}"; do
    name=$(echo $service | cut -d':' -f1)
    port=$(echo $service | cut -d':' -f2)
    
    if curl -sf http://localhost:$port/api/v1/health > /dev/null 2>&1; then
        echo "✅ $name (port $port): healthy"
    else
        echo "❌ $name (port $port): unhealthy"
    fi
done

# Check console UI
if curl -sf http://localhost:3000 > /dev/null 2>&1; then
    echo "✅ Console UI (port 3000): healthy"
else
    echo "❌ Console UI (port 3000): unhealthy"
fi

echo ""
echo "🎉 SentinelOps Platform started successfully!"
echo ""
echo "🌐 Access Points:"
echo "  Console UI:     http://localhost:3000"
echo "  API Gateway:    http://localhost:8000"
echo "  Grafana:        http://localhost:3002 (admin/admin)"
echo "  Demo App:       http://localhost:3001"
echo ""
echo "📋 Quick Start:"
echo "  1. Open Console UI: http://localhost:3000"
echo "  2. Go to Policies tab"
echo "  3. Create a new policy in English"
echo "  4. Follow the workflow: Compile → Prove → Build → Deploy"
echo "  5. Monitor in Runtime tab"
echo "  6. Check Evidence tab for certificates"
echo ""
echo "🎯 Demo:"
echo "  make demo-setup    # Set up fraud detection demo"
echo "  make demo-run      # Run demo scenarios"
echo ""
echo "🛑 To stop:"
echo "  make demo-down     # Stop all services"
echo ""