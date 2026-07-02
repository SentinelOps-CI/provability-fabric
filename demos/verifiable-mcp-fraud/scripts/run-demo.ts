// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import { MCPClientAgent } from '../src/mcp-client-agent.js';

async function runDemo() {
  console.log('Verifiable MCP Fraud Demo — run phase');
  console.log('');

  const config = {
    tenant_id: process.env.TENANT_ID || 'acme-corp',
    session_id: process.env.SESSION_ID || `demo_session_${Date.now()}`,
    policy_enforcement: true,
    sidecar_url: process.env.SIDECAR_URL || 'http://localhost:8006',
  };

  const agent = new MCPClientAgent(config);

  try {
    await agent.connect();
    await agent.runFullDemo();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error('Demo run failed:', message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  runDemo().catch((error) => {
    console.error(error);
    process.exit(1);
  });
}
