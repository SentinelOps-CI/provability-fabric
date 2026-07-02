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
import { ToolSignatureManager } from './tool-signature-manager';
import { CertificateManager } from './certificate-manager';
import { EgressProfileManager } from './egress-profile-manager';
import { JCSValidator } from './jcs-validator';
import type {
  JsonRpcRequest,
  PolicyEnforcementResult,
  McpProxyStats,
} from './types.js';
import type { McpAuthenticatedRequest } from '../types/express-mcp.js';

interface McpRequest {
  method: string;
  params: Record<string, unknown>;
  id?: string | number;
  jsonrpc?: string;
}

export class McpProxy {
  private prisma: PrismaClient;
  private logger: winston.Logger;
  private sidecarUrl: string;
  private toolSignatureManager: ToolSignatureManager;
  private certificateManager: CertificateManager;
  private egressProfileManager: EgressProfileManager;
  private jcsValidator: JCSValidator;

  constructor(
    prisma: PrismaClient, 
    logger: winston.Logger,
    sidecarUrl: string = 'http://localhost:8081'
  ) {
    this.prisma = prisma;
    this.logger = logger;
    this.sidecarUrl = sidecarUrl;
    this.toolSignatureManager = new ToolSignatureManager(logger);
    this.certificateManager = new CertificateManager(logger);
    this.egressProfileManager = new EgressProfileManager(logger);
    this.jcsValidator = new JCSValidator(logger);
  }

  /**
   * Express middleware for MCP request proxying with policy enforcement
   */
  middleware() {
    return async (req: Request, res: Response, next: NextFunction) => {
      try {
        const mcpReq = req as McpAuthenticatedRequest;
        // Parse tenant from JWT (set by auth middleware) — canonical field is tid
        const user = mcpReq.user;
        const tenantId = user?.tid ?? user?.tenantId ?? user?.tenant_id;
        const userId = user?.sub;
        const rlsTokenHash = user?.rls_token_hash;

        // Validate MCP request format
        const mcpRequest = this.validateMcpRequest(req.body);

        // Early JCS validation for input rejection
        const earlyValidation = this.performEarlyJCSValidation(mcpRequest);
        if (earlyValidation.reject) {
          this.logger.warn('MCP: Early JCS validation failed', {
            reason: earlyValidation.reason,
            method: mcpRequest.method,
            tenantId
          });

          return res.status(400).json({
            jsonrpc: '2.0',
            error: {
              code: -32600,
              message: 'Invalid request',
              data: {
                reason: earlyValidation.reason,
                type: 'jcs_validation_failed'
              }
            },
            id: mcpRequest.id
          });
        }

        // Enforce RLS claims validation
        if (tenantId && rlsTokenHash) {
          const rlsValidation = this.certificateManager.enforceRLSClaims(
            tenantId,
            rlsTokenHash,
            ['mcp_access'] // Required permission for MCP access
          );

          if (!rlsValidation.allowed) {
            this.logger.warn('MCP: RLS claims validation failed', {
              tenantId,
              rlsTokenHash: rlsTokenHash.substring(0, 16) + '...',
              reason: rlsValidation.reason,
              violations: rlsValidation.violations
            });

            return res.status(403).json({
              jsonrpc: '2.0',
              error: {
                code: -32000,
                message: 'RLS claims validation failed',
                data: {
                  reason: rlsValidation.reason,
                  violations: rlsValidation.violations
                }
              },
              id: mcpRequest.id
            });
          }
        }
        
        this.logger.info('MCP: Proxying request', {
          method: mcpRequest.method,
          tenantId,
          userId,
          requestId: mcpRequest.id
        });

        // Start timeline tracking for tool calls
        let decisionId: string | null = null;
        if (mcpRequest.method === 'tools/call') {
          const sessionId = mcpReq.sessionId || `session_${Date.now()}`;
          const toolName = (mcpRequest.params?.name as string | undefined) || 'unknown';
          decisionId = this.egressProfileManager.startDecisionTimeline(
            mcpRequest.id?.toString() || 'unknown',
            sessionId,
            tenantId || 'anonymous',
            toolName
          );
        }

        // Enforce policies through sidecar integration
        const policyResult = await this.enforcePolicy(mcpRequest, tenantId, userId);
        
        if (!policyResult.allowed) {
          // Add timeline event for policy violation
          if (decisionId) {
            this.egressProfileManager.addTimelineEvent(decisionId, 'policy_check', {
              policyResult: policyResult.reason,
              violatedConstraints: policyResult.violatedConstraints,
              requestId: mcpRequest.id?.toString(),
              sessionId: mcpReq.sessionId
            });
          }

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

        // Add timeline event for successful validation
        if (decisionId) {
          this.egressProfileManager.addTimelineEvent(decisionId, 'validation_completed', {
            policyResult: 'passed',
            requestId: mcpRequest.id?.toString(),
            sessionId: mcpReq.sessionId
          });
        }

        // Attach validated context to request
        mcpReq.mcpContext = {
          tenantId,
          userId,
          validated: true,
          policyResult,
          decisionId
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
  private validateMcpRequest(body: unknown): McpRequest {
    if (!body || typeof body !== 'object') {
      throw new Error('Invalid MCP request: missing body');
    }

    const rpc = body as JsonRpcRequest;
    if (rpc.jsonrpc !== '2.0') {
      throw new Error('Invalid MCP request: missing or invalid jsonrpc version');
    }

    if (!rpc.method || typeof rpc.method !== 'string') {
      throw new Error('Invalid MCP request: missing or invalid method');
    }

    return {
      method: rpc.method,
      params: (rpc.params as Record<string, unknown>) || {},
      id: rpc.id,
      jsonrpc: rpc.jsonrpc
    };
  }

  /**
   * Perform early JCS validation for input rejection
   */
  private performEarlyJCSValidation(request: McpRequest): { reject: boolean; reason?: string } {
    try {
      // Get appropriate schema based on method
      let schemaName: string;
      switch (request.method) {
        case 'tools/call':
          schemaName = 'tool_call';
          break;
        case 'resources/read':
          schemaName = 'tenant_context';
          break;
        default:
          return {
            reject: true,
            reason: `Unknown MCP method: ${request.method}`,
          };
      }

      const schema = this.jcsValidator.getSchema(schemaName);
      if (!schema) {
        return { reject: false }; // No schema available, skip validation
      }

      // Early rejection check
      const earlyReject = this.jcsValidator.earlyReject(request.params, schema);
      if (earlyReject.reject) {
        return earlyReject;
      }

      // Full JCS validation for tool calls
      if (request.method === 'tools/call') {
        const validation = this.jcsValidator.validateInput(request.params, schema, {
          strictMode: true,
          allowAdditionalProperties: false
        });

        if (!validation.valid) {
          return {
            reject: true,
            reason: `JCS validation failed: ${validation.errors.join(', ')}`
          };
        }
      }

      return { reject: false };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      return {
        reject: true,
        reason: `JCS validation error: ${errorMessage}`
      };
    }
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
      const methodPolicyResult = await this.enforceMethodPolicy(request, tenantId);
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
  private async enforceMethodPolicy(request: McpRequest, tenantId?: string): Promise<PolicyEnforcementResult> {
    const { method, params } = request;

    switch (method) {
      case 'tools/call':
        return this.enforceToolCallPolicy(params, tenantId);
      
      case 'resources/read':
        return this.enforceResourceReadPolicy(params);
      
      case 'tools/list':
      case 'resources/list':
        // List operations are generally safe
        return { allowed: true };
      
      default:
        // Deny unknown MCP methods by default
        this.logger.warn('MCP: Unknown method denied', { method });
        return {
          allowed: false,
          reason: `Unknown MCP method: ${method}`,
          violatedConstraints: ['unknown_method'],
        };
    }
  }

  /**
   * Enforce policies for tool calls with tool signature validation
   */
  private async enforceToolCallPolicy(params: Record<string, unknown>, tenantId?: string): Promise<PolicyEnforcementResult> {
    const toolName = params.name;
    const toolArgs = params.arguments;
    if (typeof toolName !== 'string') {
      return {
        allowed: false,
        reason: 'Tool call missing name',
        violatedConstraints: ['tool_name_required'],
      };
    }

    const argsRecord =
      toolArgs && typeof toolArgs === 'object' && !Array.isArray(toolArgs)
        ? (toolArgs as Record<string, unknown>)
        : {};

    // Get current epoch (simplified - in production, this would come from a time service)
    const epoch = Math.floor(Date.now() / (60 * 1000)); // 1-minute epochs

    // Validate tool call using tool signature manager
    const validationResult = this.toolSignatureManager.validateToolCall(
      toolName,
      argsRecord,
      tenantId || 'anonymous',
      epoch
    );

    if (!validationResult.allowed) {
      return {
        allowed: false,
        reason: validationResult.reason,
        violatedConstraints: ['tool_signature_validation']
      };
    }

    // Additional sidecar constraint checks
    if (validationResult.toolSignature) {
      const sidecarResult = this.toolSignatureManager.checkSidecarConstraints(
        validationResult.toolSignature,
        tenantId || 'anonymous',
        epoch
      );

      if (!sidecarResult.allowed) {
        return {
          allowed: false,
          reason: sidecarResult.reason,
          violatedConstraints: sidecarResult.constraints || ['sidecar_constraint']
        };
      }
    }

    this.logger.info('MCP: Tool call policy enforcement passed', {
      toolName,
      toolSignature: validationResult.toolSignature,
      tenantId,
      epoch
    });

    return { allowed: true };
  }

  /**
   * Enforce policies for resource reads
   */
  private async enforceResourceReadPolicy(params: Record<string, unknown>): Promise<PolicyEnforcementResult> {
    const uri = params.uri;
    if (typeof uri !== 'string') {
      return {
        allowed: false,
        reason: 'Resource read missing uri',
        violatedConstraints: ['uri_required'],
      };
    }

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
    params: Record<string, unknown>;
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
  async getStats(tenantId?: string): Promise<McpProxyStats> {
    // Clean up expired entries
    this.toolSignatureManager.cleanupExpiredEntries();
    this.certificateManager.cleanupExpiredEntries();
    this.egressProfileManager.cleanupOldExplanations();
    this.jcsValidator.clearCache();
    
    // Get component stats
    const toolStats = this.toolSignatureManager.getCacheStats();
    const certStats = this.certificateManager.getStats();
    const egressStats = this.egressProfileManager.getStats();
    const jcsStats = this.jcsValidator.getStats();
    
    // Return proxy statistics for monitoring dashboard
    return {
      totalRequests: 0, // TODO: Implement counters
      blockedRequests: 0,
      averageResponseTime: 0,
      tenantId,
      timestamp: new Date().toISOString(),
      toolSignatureManager: toolStats,
      certificateManager: certStats,
      egressProfileManager: egressStats,
      jcsValidator: jcsStats
    };
  }
}

export default McpProxy;
