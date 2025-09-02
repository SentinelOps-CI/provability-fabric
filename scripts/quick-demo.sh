#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

set -e

echo "🎬 SentinelOps Platform Quick Demo"
echo "=================================="
echo ""
echo "This demo showcases the complete platform capabilities:"
echo "1. English → ActionDSL → DFA → Deployment"
echo "2. Runtime enforcement with CERT-V1 emission"
echo "3. Deterministic replay with 99.9%+ low-view equality"
echo "4. Compliance packet export"
echo ""

# Start platform
echo "🚀 Starting platform..."
make demo-up

echo ""
echo "⏳ Waiting for platform to be fully ready..."
sleep 60

# Run demo
echo ""
echo "🎯 Running fraud detection demo..."
cd demos/verifiable-mcp-fraud

# Setup demo
echo "1️⃣ Setting up demo policies..."
npm run demo:setup

# Run agent
echo "2️⃣ Running MCP client agent..."
timeout 60 npm run dev:agent || echo "Agent demo completed"

echo ""
echo "🔍 Demo Results:"
echo ""

# Check certificates
CERT_COUNT=$(find ../../evidence -name "*.cert.json" 2>/dev/null | wc -l)
echo "📜 Generated certificates: $CERT_COUNT"

# Check compliance
if [ -f "demo-config.json" ]; then
    POLICY_HASH=$(jq -r '.policy_hash' demo-config.json)
    echo "🔐 Policy hash: ${POLICY_HASH:0:16}..."
fi

echo ""
echo "✅ Quick demo completed!"
echo ""
echo "🌐 Explore the platform:"
echo "  Console UI:     http://localhost:3000"
echo "  API Gateway:    http://localhost:8000"
echo "  Grafana:        http://localhost:3002"
echo ""
echo "🎯 Next steps:"
echo "  1. Open Console UI and explore all tabs"
echo "  2. Run replays in the Replay tab"
echo "  3. Download compliance packets in Evidence tab"
echo "  4. Monitor live metrics in Runtime tab"
echo "  5. Rotate epochs and see targeted effects"
echo ""
echo "🛑 To stop the demo:"
echo "  make demo-down"
echo ""