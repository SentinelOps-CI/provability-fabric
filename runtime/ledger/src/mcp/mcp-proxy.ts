/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * MCP Proxy for Sidecar Integration
 * Provides policy enforcement and audit logging for MCP requests
 */

import { Request, Response, NextFunction } from 'express';
import { PrismaClient } from '@prisma/client';
import winston from 'winston';
import axios from 'axios';

interface McpRequest {
  method: string;
  params: any;
  id?: string | number;
  jsonrpc?: string;
}

interface McpResponse {
  result?: any;
  error?: {
    code: number;
    message: string;
    data?: any;
  };
  id?: string | number;
  jsonrpc?: string;
}

interface PolicyEnforcementResult {
  allowed: boolean;
  reason?: string;
  violatedConstraints?: string[];
}

export class McpProxy {
  private prisma: PrismaClient;
  private logger: winston.Logger;
  private sidecarUrl: string;

  constructor(
    prisma: PrismaClient, 
    logger: winston.Logger,
    sidecarUrl: string = 'http://localhost:8081'
  ) {
    this.prisma = prisma;
    this.logger = logger;
    this.sidecarUrl = sidecarUrl;
  }

  /**
   * Express middleware for MCP request proxying with policy enforcement
   */
  middleware() {
    return async (req: Request, res: Response, next: NextFunction) => {
      try {
        // Parse tenant from JWT (set by auth middleware)
        const tenantId = (req as any).user?.tenant_id;
        const userId = (req as any).user?.sub;

        // Validate MCP request format
        const mcpRequest = this.validateMcpRequest(req.body);
        
        this.logger.info('MCP: Proxying request', {
          method: mcpRequest.method,
          tenantId,
          userId,
          requestId: mcpRequest.id
        });

        // Enforce policies through sidecar integration
        const policyResult = await this.enforcePolicy(mcpRequest, tenantId, userId);
        
        if (!policyResult.allowed) {
          this.logger.warn('MCP: Request blocked by policy', {
            method: mcpRequest.method,
            reason: policyResult.reason,
            tenantId,
            userId
          });

          return res.status(403).json({
            jsonrpc: '2.0',
            error: {
              code: -32000,
              message: 'Policy violation',
              data: {
                reason: policyResult.reason,
                violatedConstraints: policyResult.violatedConstraints
              }
            },
            id: mcpRequest.id
          });
        }

        // Log audit event
        await this.logAuditEvent({
          eventType: 'mcp_request',
          method: mcpRequest.method,
          tenantId,
          userId,
          params: mcpRequest.params,
          timestamp: new Date(),
          requestId: mcpRequest.id
        });

        // Attach validated context to request
        (req as any).mcpContext = {
          tenantId,
          userId,
          validated: true,
          policyResult
        };

        next();
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        const errorStack = error instanceof Error ? error.stack : undefined;
        this.logger.error('MCP: Proxy middleware error', {
          error: errorMessage,
          stack: errorStack
        });

        res.status(500).json({
          jsonrpc: '2.0',
          error: {
            code: -32603,
            message: 'Internal error'
          },
          id: req.body?.id
        });
      }
    };
  }

  /**
   * Validate MCP request format according to JSON-RPC 2.0 spec
   */
  private validateMcpRequest(body: any): McpRequest {
    if (!body || typeof body !== 'object') {
      throw new Error('Invalid MCP request: missing body');
    }

    if (body.jsonrpc !== '2.0') {
      throw new Error('Invalid MCP request: missing or invalid jsonrpc version');
    }

    if (!body.method || typeof body.method !== 'string') {
      throw new Error('Invalid MCP request: missing or invalid method');
    }

    return {
      method: body.method,
      params: body.params || {},
      id: body.id,
      jsonrpc: body.jsonrpc
    };
  }

  /**
   * Enforce provability-fabric policies for MCP requests
   */
  private async enforcePolicy(
    request: McpRequest, 
    tenantId?: string, 
    userId?: string
  ): Promise<PolicyEnforcementResult> {
    try {
      // Check tenant-specific quotas and constraints
      if (tenantId) {
        const tenantQuota = await this.checkTenantQuota(tenantId);
        if (!tenantQuota.allowed) {
          return {
            allowed: false,
            reason: 'Tenant quota exceeded',
            violatedConstraints: ['tenant_quota_limit']
          };
        }
      }

      // Rate limiting based on method type
      const rateLimitResult = await this.checkRateLimit(request.method, tenantId, userId);
      if (!rateLimitResult.allowed) {
        return {
          allowed: false,
          reason: 'Rate limit exceeded',
          violatedConstraints: ['rate_limit']
        };
      }

      // Method-specific policy enforcement
      const methodPolicyResult = await this.enforceMethodPolicy(request);
      if (!methodPolicyResult.allowed) {
        return methodPolicyResult;
      }

      // Integrate with sidecar for advanced constraint checking
      const sidecarResult = await this.checkSidecarConstraints(request, tenantId);
      if (!sidecarResult.allowed) {
        return sidecarResult;
      }

      return { allowed: true };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: Policy enforcement error', {
        error: errorMessage,
        method: request.method,
        tenantId,
        userId
      });

      // Fail secure - deny on policy enforcement errors
      return {
        allowed: false,
        reason: 'Policy enforcement system error',
        violatedConstraints: ['system_error']
      };
    }
  }

  /**
   * Check tenant-specific quotas
   */
  private async checkTenantQuota(tenantId: string): Promise<PolicyEnforcementResult> {
    try {
      // Check current usage against tenant limits
      const usage = await this.prisma.capsule.count({
        where: { tenantId }
      });

      // Simple quota check (extend based on tenant plan)
      const maxCapsules = 100; // Default limit
      
      if (usage >= maxCapsules) {
        return {
          allowed: false,
          reason: `Tenant quota exceeded: ${usage}/${maxCapsules} capsules`,
          violatedConstraints: ['max_capsules']
        };
      }

      return { allowed: true };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: Tenant quota check failed', {
        error: errorMessage,
        tenantId
      });
      
      return {
        allowed: false,
        reason: 'Quota check system error',
        violatedConstraints: ['quota_system_error']
      };
    }
  }

  /**
   * Check rate limits for MCP methods
   */
  private async checkRateLimit(
    method: string, 
    tenantId?: string, 
    userId?: string
  ): Promise<PolicyEnforcementResult> {
    // Simple in-memory rate limiting (use Redis for production)
    const key = `mcp_rate_limit:${tenantId || 'anonymous'}:${method}`;
    
    // Rate limits per method type
    const rateLimits: Record<string, { requests: number; window: number }> = {
      'tools/call': { requests: 100, window: 60 }, // 100 requests per minute
      'tools/list': { requests: 10, window: 60 },  // 10 requests per minute
      'resources/read': { requests: 50, window: 60 }, // 50 requests per minute
      'default': { requests: 20, window: 60 } // Default limit
    };

    const limit = rateLimits[method] || rateLimits.default;
    
    // TODO: Implement proper rate limiting with sliding window
    // For now, just log and allow
    this.logger.debug('MCP: Rate limit check', {
      method,
      limit,
      tenantId,
      userId
    });

    return { allowed: true };
  }

  /**
   * Method-specific policy enforcement
   */
  private async enforceMethodPolicy(request: McpRequest): Promise<PolicyEnforcementResult> {
    const { method, params } = request;

    switch (method) {
      case 'tools/call':
        return this.enforceToolCallPolicy(params);
      
      case 'resources/read':
        return this.enforceResourceReadPolicy(params);
      
      case 'tools/list':
      case 'resources/list':
        // List operations are generally safe
        return { allowed: true };
      
      default:
        this.logger.warn('MCP: Unknown method, applying default policy', { method });
        return { allowed: true };
    }
  }

  /**
   * Enforce policies for tool calls
   */
  private async enforceToolCallPolicy(params: any): Promise<PolicyEnforcementResult> {
    const { name: toolName, arguments: toolArgs } = params;

    // Validate tool arguments based on tool type
    switch (toolName) {
      case 'query_capsules':
        // Ensure reasonable query limits
        if (toolArgs?.limit && toolArgs.limit > 1000) {
          return {
            allowed: false,
            reason: 'Query limit too high',
            violatedConstraints: ['max_query_limit']
          };
        }
        break;

      case 'verify_behavior_guarantee':
        // Ensure required parameters are present
        if (!toolArgs?.capsuleId || !toolArgs?.behaviorSpec) {
          return {
            allowed: false,
            reason: 'Missing required parameters for behavior verification',
            violatedConstraints: ['required_parameters']
          };
        }
        break;

      case 'log_audit_event':
        // Validate audit event severity
        const validSeverities = ['info', 'warning', 'error', 'critical'];
        if (toolArgs?.severity && !validSeverities.includes(toolArgs.severity)) {
          return {
            allowed: false,
            reason: 'Invalid audit event severity',
            violatedConstraints: ['valid_severity']
          };
        }
        break;
    }

    return { allowed: true };
  }

  /**
   * Enforce policies for resource reads
   */
  private async enforceResourceReadPolicy(params: any): Promise<PolicyEnforcementResult> {
    const { uri } = params;

    // Validate URI patterns
    const allowedUriPatterns = [
      /^provability:\/\/capsules\/.+$/,
      /^provability:\/\/proofs\/.+$/,
      /^provability:\/\/audit\/.+$/
    ];

    const isAllowed = allowedUriPatterns.some(pattern => pattern.test(uri));
    
    if (!isAllowed) {
      return {
        allowed: false,
        reason: 'Unauthorized resource URI',
        violatedConstraints: ['allowed_uri_patterns']
      };
    }

    return { allowed: true };
  }

  /**
   * Check constraints via sidecar integration
   */
  private async checkSidecarConstraints(
    request: McpRequest,
    tenantId?: string
  ): Promise<PolicyEnforcementResult> {
    try {
      // Send request to sidecar for advanced constraint checking
      const sidecarResponse = await axios.post(`${this.sidecarUrl}/check-constraints`, {
        mcpRequest: request,
        tenantId,
        timestamp: new Date().toISOString()
      }, {
        timeout: 5000,
        headers: {
          'Content-Type': 'application/json'
        }
      });

      const { allowed, violations } = sidecarResponse.data;
      
      if (!allowed) {
        return {
          allowed: false,
          reason: 'Sidecar constraint violations detected',
          violatedConstraints: violations || ['sidecar_constraint']
        };
      }

      return { allowed: true };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.warn('MCP: Sidecar constraint check failed, allowing request', {
        error: errorMessage,
        method: request.method,
        tenantId
      });

      // Fail open for sidecar connectivity issues (configurable)
      return { allowed: true };
    }
  }

  /**
   * Log audit events for MCP interactions
   */
  private async logAuditEvent(event: {
    eventType: string;
    method: string;
    tenantId?: string;
    userId?: string;
    params: any;
    timestamp: Date;
    requestId?: string | number;
  }): Promise<void> {
    try {
      // In production, store to audit database
      this.logger.info('MCP: Audit event', {
        ...event,
        source: 'mcp_proxy'
      });

      // Could also send to external audit system
      // await this.sendToAuditSystem(event);
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: Failed to log audit event', {
        error: errorMessage,
        event
      });
    }
  }

  /**
   * Get proxy statistics for monitoring
   */
  async getStats(tenantId?: string): Promise<any> {
    // Return proxy statistics for monitoring dashboard
    return {
      totalRequests: 0, // TODO: Implement counters
      blockedRequests: 0,
      averageResponseTime: 0,
      tenantId,
      timestamp: new Date().toISOString()
    };
  }
}

export default McpProxy;
