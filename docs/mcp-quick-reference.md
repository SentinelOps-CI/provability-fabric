# MCP Quick Reference Guide

**Provability-Fabric Model Context Protocol Quick Reference**

## Quick Start

### 1. Start the MCP Service
```bash
cd runtime/ledger
npm run dev
# Service available at http://localhost:4000/api/mcp
```

### 2. Basic Health Check
```bash
curl http://localhost:4000/api/mcp/health
```

### 3. List Available Tools
```bash
curl -X POST http://localhost:4000/api/mcp/jsonrpc \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer YOUR_JWT_TOKEN" \
  -d '{
    "jsonrpc": "2.0",
    "method": "tools/list",
    "params": {},
    "id": 1
  }'
```

## Common MCP Requests

### Query Agent Capsules
```json
{
  "jsonrpc": "2.0",
  "method": "tools/call",
  "params": {
    "name": "query_capsules",
    "arguments": {
      "filter": { "tenantId": "your-tenant" },
      "limit": 10
    }
  },
  "id": 1
}
```

### Verify Behavioral Guarantee
```json
{
  "jsonrpc": "2.0",
  "method": "tools/call", 
  "params": {
    "name": "verify_behavior_guarantee",
    "arguments": {
      "capsuleId": "capsule-123",
      "behaviorSpec": "privacy_budget <= 1.0",
      "proofType": "lean"
    }
  },
  "id": 2
}
```

### Log Audit Event
```json
{
  "jsonrpc": "2.0",
  "method": "tools/call",
  "params": {
    "name": "log_audit_event",
    "arguments": {
      "eventType": "agent_action",
      "agentId": "agent-456", 
      "details": { "action": "data_query" },
      "severity": "info"
    }
  },
  "id": 3
}
```

### Read Resource
```json
{
  "jsonrpc": "2.0",
  "method": "resources/read",
  "params": {
    "uri": "provability://capsules/active"
  },
  "id": 4
}
```

## Constraint Violations

### Query Limit Exceeded
```json
// Request with limit > 1000 will be blocked
{
  "jsonrpc": "2.0",
  "error": {
    "code": -32000,
    "message": "Policy violation",
    "data": {
      "reason": "Query limit too high",
      "violatedConstraints": ["max_query_limit"]
    }
  },
  "id": 1
}
```

### Unauthorized Resource Access
```json
// Invalid URI pattern will be blocked
{
  "jsonrpc": "2.0",
  "error": {
    "code": -32000,
    "message": "Policy violation", 
    "data": {
      "reason": "Unauthorized resource URI",
      "violatedConstraints": ["allowed_uri_patterns"]
    }
  },
  "id": 2
}
```

## WebSocket Real-time Monitoring

### Connect and Subscribe
```javascript
const ws = new WebSocket('ws://localhost:4000/mcp/ws');

ws.on('open', () => {
  ws.send(JSON.stringify({
    type: 'subscribe',
    tenantId: 'your-tenant',
    eventTypes: ['constraint_violations', 'audit_events']
  }));
});

ws.on('message', (data) => {
  const event = JSON.parse(data.toString());
  console.log('Real-time event:', event);
});
```

## Available Tools

| Tool Name | Purpose | Required Args | Optional Args |
|-----------|---------|---------------|---------------|
| `query_capsules` | Query agent capsules | - | `filter`, `limit` |
| `verify_behavior_guarantee` | Verify formal guarantees | `capsuleId`, `behaviorSpec` | `proofType` |
| `log_audit_event` | Record audit events | `eventType`, `agentId`, `details` | `severity` |

## Available Resources

| URI Pattern | Description | Content Type |
|-------------|-------------|--------------|
| `provability://capsules/active` | Active agent capsules | `application/json` |
| `provability://proofs/lean` | Lean behavioral proofs | `text/plain` |
| `provability://audit/events` | Audit trail events | `application/json` |

## Rate Limits

| Method | Requests | Window |
|--------|----------|--------|
| `tools/call` | 100 | 60 seconds |
| `tools/list` | 10 | 60 seconds |
| `resources/read` | 50 | 60 seconds |

## Security Requirements

1. **Authentication**: Include JWT token in `Authorization` header
2. **HTTPS**: Use HTTPS in production environments
3. **Tenant Isolation**: Requests are automatically scoped to user's tenant
4. **Input Validation**: All parameters are validated and sanitized

## Error Codes

| Code | Name | Description |
|------|------|-------------|
| -32600 | Invalid Request | Missing required fields |
| -32601 | Method Not Found | Unknown method or tool |
| -32602 | Invalid Params | Invalid parameter format |
| -32603 | Internal Error | Server-side error |
| -32000 | Policy Violation | Constraint enforcement blocked request |

## Environment Variables

```bash
# Essential Configuration
SIDECAR_URL=http://localhost:8081
MCP_ENABLE_WEBSOCKET=true
MCP_ENABLE_MULTI_TENANT=true

# Rate Limiting
MCP_TOOLS_CALL_LIMIT=100
MCP_TOOLS_LIST_LIMIT=10
MCP_RESOURCES_READ_LIMIT=50

# Security
MCP_MAX_QUERY_LIMIT=1000
```

## Testing Commands

```bash
# Run comprehensive test suite
cd runtime/ledger
node test-mcp-comprehensive.js

# Run basic integration tests  
node test-mcp-integration.js

# Start test server for development
node start-test-server.js
```

## Debugging

```bash
# Enable debug logging
export LOG_LEVEL=debug

# Check service health
curl http://localhost:4000/api/mcp/health

# View real-time logs
tail -f runtime/ledger/mcp-service.log

# Check running processes
netstat -an | findstr :4000
```

## TypeScript SDK Example

```typescript
import { McpClient } from '@modelcontextprotocol/sdk/client';

class ProvabilityFabricMcpClient {
  private client: McpClient;
  private baseUrl: string;
  private authToken: string;

  constructor(baseUrl: string, authToken: string) {
    this.baseUrl = baseUrl;
    this.authToken = authToken;
    this.client = new McpClient();
  }

  async queryCapsules(filter: any = {}, limit: number = 10) {
    return await this.client.request({
      method: 'tools/call',
      params: {
        name: 'query_capsules',
        arguments: { filter, limit }
      }
    });
  }

  async verifyBehavior(capsuleId: string, behaviorSpec: string) {
    return await this.client.request({
      method: 'tools/call',
      params: {
        name: 'verify_behavior_guarantee', 
        arguments: { capsuleId, behaviorSpec, proofType: 'lean' }
      }
    });
  }
}

// Usage
const client = new ProvabilityFabricMcpClient(
  'http://localhost:4000/api/mcp',
  'your-jwt-token'
);

const capsules = await client.queryCapsules();
console.log('Available capsules:', capsules.result);
```

## Architecture Files

| File | Purpose |
|------|---------|
| `runtime/ledger/src/mcp/mcp-server.ts` | Core MCP server implementation |
| `runtime/ledger/src/mcp/mcp-proxy.ts` | Policy enforcement and security |
| `runtime/ledger/src/mcp/mcp-service.ts` | Service orchestration |
| `runtime/ledger/src/index.ts` | Main integration point |

For complete documentation, see [MCP Integration Guide](./mcp-integration.md).
