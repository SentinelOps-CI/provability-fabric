# MCP Migration Guide

**Migrating to Provability-Fabric Model Context Protocol Integration**  
*Version: 2.1.0*

## Overview

This guide helps you migrate existing AI agent integrations to use the new Model Context Protocol (MCP) interface while maintaining all existing behavioral constraints and security guarantees.

## Migration Timeline

- **Phase 1**: Update to v2.1.0 (MCP available alongside existing APIs)
- **Phase 2**: Migrate agent interactions to MCP (gradual migration)
- **Phase 3**: Deprecate direct API access (future version)

## What's Changed

### New MCP Endpoints

```bash
# New MCP endpoints (v2.1.0+)
POST /api/mcp/jsonrpc          # Main MCP JSON-RPC endpoint
GET  /api/mcp/health           # MCP service health
GET  /api/mcp/servers          # MCP server discovery
GET  /api/mcp/stats            # MCP usage statistics
ws://localhost:4000/mcp/ws     # MCP WebSocket events
```

### Existing Endpoints (Still Available)

```bash
# Existing endpoints (continue to work)
GET  /tenant/:tid/capsules     # Direct capsule access
POST /tenant/:tid/quote/:hash  # Premium quote generation
POST /graphql                  # GraphQL interface
POST /usage                    # Billing endpoints
```

## Migration Steps

### Step 1: Update Dependencies

```bash
# Install MCP SDK
npm install @modelcontextprotocol/sdk

# Update Provability-Fabric
git pull origin main
cd runtime/ledger
npm install
```

### Step 2: Verify MCP Service

```bash
# Start updated service
npm run dev

# Verify MCP health
curl http://localhost:4000/api/mcp/health
```

Expected response:
```json
{
  "status": "healthy",
  "servers": 1,
  "timestamp": "2025-01-27T10:30:00Z",
  "version": "1.0.0"
}
```

### Step 3: Migrate Agent Code

#### Before (Direct API):
```typescript
// Old approach - direct REST API calls
const response = await fetch('/tenant/123/capsules', {
  headers: {
    'Authorization': `Bearer ${token}`
  }
});
const capsules = await response.json();
```

#### After (MCP):
```typescript
// New approach - MCP tools
import { McpClient } from '@modelcontextprotocol/sdk/client';

const client = new McpClient();
const response = await client.request({
  method: 'tools/call',
  params: {
    name: 'query_capsules',
    arguments: {
      filter: { tenantId: '123' },
      limit: 10
    }
  }
});
const capsules = JSON.parse(response.result.content[0].text);
```

### Step 4: Update Authentication

#### Before:
```typescript
// Direct bearer token
headers: {
  'Authorization': `Bearer ${token}`
}
```

#### After:
```typescript
// Same JWT token, applied to MCP requests
const mcpRequest = {
  jsonrpc: '2.0',
  method: 'tools/call',
  params: { /* ... */ },
  id: 1
};

const response = await axios.post('/api/mcp/jsonrpc', mcpRequest, {
  headers: {
    'Authorization': `Bearer ${token}`,
    'Content-Type': 'application/json'
  }
});
```

### Step 5: Implement Error Handling

#### New Constraint Violation Handling:
```typescript
try {
  const response = await mcpClient.request(mcpRequest);
  return response.result;
} catch (error) {
  if (error.code === -32000) { // Policy violation
    console.log('Constraint violated:', error.data.reason);
    console.log('Violated constraints:', error.data.violatedConstraints);
    // Implement fallback or user notification
  }
  throw error;
}
```

## Migration Examples

### 1. Capsule Queries

**Before:**
```typescript
async function getCapsules(tenantId: string, limit: number = 10) {
  const response = await fetch(`/tenant/${tenantId}/capsules?limit=${limit}`);
  return await response.json();
}
```

**After:**
```typescript
async function getCapsules(tenantId: string, limit: number = 10) {
  return await mcpClient.request({
    method: 'tools/call',
    params: {
      name: 'query_capsules',
      arguments: {
        filter: { tenantId },
        limit
      }
    }
  });
}
```

### 2. Behavioral Verification

**Before:**
```typescript
// Custom verification implementation
async function verifyBehavior(capsuleId: string, spec: string) {
  // Custom logic to check behavioral specifications
}
```

**After:**
```typescript
async function verifyBehavior(capsuleId: string, behaviorSpec: string) {
  return await mcpClient.request({
    method: 'tools/call',
    params: {
      name: 'verify_behavior_guarantee',
      arguments: {
        capsuleId,
        behaviorSpec,
        proofType: 'lean'
      }
    }
  });
}
```

### 3. Audit Logging

**Before:**
```typescript
// Manual audit logging
async function logEvent(event: AuditEvent) {
  await fetch('/audit/events', {
    method: 'POST',
    body: JSON.stringify(event)
  });
}
```

**After:**
```typescript
async function logEvent(eventType: string, agentId: string, details: any) {
  return await mcpClient.request({
    method: 'tools/call',
    params: {
      name: 'log_audit_event',
      arguments: {
        eventType,
        agentId,
        details,
        severity: 'info'
      }
    }
  });
}
```

## Real-time Monitoring Migration

### Before:
```typescript
// Custom WebSocket implementation
const ws = new WebSocket('ws://localhost:8081');
ws.on('message', handleCustomMessage);
```

### After:
```typescript
// MCP WebSocket with structured events
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
  if (event.type === 'mcp_event') {
    handleMcpEvent(event.event);
  }
});
```

## Configuration Updates

### Environment Variables

Add to your `.env` file:
```bash
# MCP Configuration
SIDECAR_URL=http://localhost:8081
MCP_ENABLE_WEBSOCKET=true
MCP_ENABLE_MULTI_TENANT=true

# Rate Limiting (optional)
MCP_TOOLS_CALL_LIMIT=100
MCP_TOOLS_LIST_LIMIT=10
MCP_RESOURCES_READ_LIMIT=50

# Security (optional)
MCP_MAX_QUERY_LIMIT=1000
MCP_ALLOWED_URI_PATTERNS=provability://.*
```

### Service Configuration

Update your service startup (if running from source):
```typescript
// In your main application
import McpService from './mcp/mcp-service.js';

const mcpService = new McpService({
  name: 'my-app-mcp',
  version: '1.0.0',
  description: 'MCP integration for my application',
  enableWebSocket: true,
  sidecarUrl: process.env.SIDECAR_URL,
  enableMultiTenant: true
}, prisma, logger);

await mcpService.initialize();
app.use('/api', mcpService.getRouter());
```

## Testing Migration

### 1. Parallel Testing

Test both old and new approaches during migration:

```typescript
async function parallelTest() {
  // Test old approach
  const oldResult = await fetch('/tenant/123/capsules');
  
  // Test new approach
  const newResult = await mcpClient.request({
    method: 'tools/call',
    params: {
      name: 'query_capsules',
      arguments: { filter: { tenantId: '123' } }
    }
  });
  
  // Compare results
  console.log('Results match:', deepEqual(oldResult, newResult));
}
```

### 2. Constraint Testing

Verify constraint enforcement works:

```typescript
async function testConstraints() {
  try {
    // This should be blocked
    await mcpClient.request({
      method: 'tools/call',
      params: {
        name: 'query_capsules',
        arguments: { limit: 50000 } // Exceeds limit
      }
    });
    console.log('ERROR: Should have been blocked!');
  } catch (error) {
    if (error.code === -32000) {
      console.log('✅ Constraint enforcement working');
    }
  }
}
```

### 3. Performance Testing

Compare performance:

```typescript
async function performanceTest() {
  // Old approach timing
  const oldStart = Date.now();
  await fetch('/tenant/123/capsules');
  const oldTime = Date.now() - oldStart;
  
  // New approach timing
  const newStart = Date.now();
  await mcpClient.request(/* MCP request */);
  const newTime = Date.now() - newStart;
  
  console.log(`Old: ${oldTime}ms, New: ${newTime}ms`);
}
```

## Breaking Changes

### None in v2.1.0

All existing APIs continue to work. MCP is additive.

### Future Deprecations (v3.0.0+)

- Direct tenant API endpoints will be deprecated
- Custom WebSocket protocols will be replaced with MCP events
- Manual audit logging will be replaced with MCP audit tools

## Rollback Plan

If issues occur, you can disable MCP:

```bash
# Disable MCP temporarily
export MCP_ENABLE_WEBSOCKET=false
export MCP_ENABLE_MULTI_TENANT=false

# Restart service
npm run dev
```

All existing functionality remains available.

## Benefits After Migration

### 1. Standardized Interface
- Industry-standard MCP protocol
- Better interoperability with other AI tools
- Consistent error handling and response format

### 2. Enhanced Security
- Real-time constraint enforcement
- Comprehensive audit logging
- Multi-layer policy validation

### 3. Better Monitoring
- Live violation alerts
- Performance metrics
- Structured event logging

### 4. Future-Proof
- Standards-compliant implementation
- Easy integration with new AI tools
- Scalable architecture

## Support and Troubleshooting

### Common Issues

1. **MCP endpoints returning 404**
   - Verify service is running with v2.1.0+
   - Check `/api/mcp/health` endpoint

2. **Authentication failures**
   - Ensure JWT token is included in Authorization header
   - Verify token is valid and not expired

3. **Constraint violations**
   - Check logs for specific violation reasons
   - Review rate limits and query constraints
   - Implement proper error handling

### Getting Help

1. Check the [MCP Integration Documentation](./integration.md)
2. Review the [MCP Quick Reference](./quick-reference.md)
3. Run diagnostic tests:
   ```bash
   cd runtime/ledger
   node test-mcp-comprehensive.js
   ```

### Migration Checklist

- [ ] Update to Provability-Fabric v2.1.0
- [ ] Install MCP SDK dependencies
- [ ] Verify MCP service health
- [ ] Update environment configuration
- [ ] Migrate authentication to include MCP endpoints
- [ ] Convert API calls to MCP tools
- [ ] Update WebSocket event handling
- [ ] Implement constraint violation error handling
- [ ] Test constraint enforcement
- [ ] Update monitoring and alerting
- [ ] Train team on new MCP interfaces
- [ ] Update documentation and runbooks
