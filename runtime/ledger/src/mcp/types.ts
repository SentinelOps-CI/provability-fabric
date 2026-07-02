/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Shared MCP / JSON-RPC types for ledger MCP modules (F27).
 */

export type JsonPrimitive = string | number | boolean | null;
export type JsonObject = { [key: string]: JsonValue };
export type JsonValue = JsonPrimitive | JsonValue[] | JsonObject;

export interface JsonRpcRequest {
  jsonrpc: '2.0';
  method: string;
  params?: Record<string, unknown>;
  id?: string | number;
}

export interface JsonRpcError {
  code: number;
  message: string;
  data?: unknown;
}

export interface JsonRpcResponse {
  jsonrpc: '2.0';
  result?: unknown;
  error?: JsonRpcError;
  id?: string | number;
}

export interface ToolCallParams {
  name: string;
  arguments?: Record<string, unknown>;
}

export interface ResourceReadParams {
  uri: string;
}

export interface McpJwtUser {
  sub?: string;
  tid?: string;
  tenantId?: string;
  tenant_id?: string;
  rls_token_hash?: string;
  email?: string;
}

export interface PolicyEnforcementResult {
  allowed: boolean;
  reason?: string;
  violatedConstraints?: string[];
}

export interface McpContext {
  tenantId?: string;
  userId?: string;
  validated: boolean;
  policyResult: PolicyEnforcementResult;
  decisionId: string | null;
}

export interface McpProxyStats {
  totalRequests: number;
  blockedRequests: number;
  averageResponseTime: number;
  tenantId?: string;
  timestamp: string;
  toolSignatureManager: Record<string, unknown>;
  certificateManager: Record<string, unknown>;
  egressProfileManager: Record<string, unknown>;
  jcsValidator: Record<string, unknown>;
}

export interface McpServiceMetrics {
  servers: number;
  connections: number;
  uptime: number;
  timestamp: string;
}

export interface McpWebSocketMessage {
  type: string;
  tenantId?: string;
  eventTypes?: string[];
  mcpRequest?: JsonRpcRequest;
}
