/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * MCP Server Integration for Provability-Fabric
 * Leverages official MCP TypeScript SDK for standardized AI-external system communication
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  ListToolsRequestSchema,
  CallToolRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
  McpError,
  ErrorCode,
} from '@modelcontextprotocol/sdk/types.js';
import { PrismaClient } from '@prisma/client';
import winston from 'winston';

interface McpServerConfig {
  name: string;
  version: string;
  description: string;
  tenantId?: string;
}

export class ProvabilityFabricMcpServer {
  private server: Server;
  private prisma: PrismaClient;
  private logger: winston.Logger;
  private tenantId?: string;

  constructor(config: McpServerConfig, prisma: PrismaClient, logger: winston.Logger) {
    this.prisma = prisma;
    this.logger = logger;
    this.tenantId = config.tenantId;

    // Initialize MCP server with provability-fabric metadata
    this.server = new Server(
      {
        name: config.name,
        version: config.version,
        description: config.description,
      },
      {
        capabilities: {
          tools: {},
          resources: {},
        },
      }
    );

    this.setupHandlers();
  }

  private setupHandlers(): void {
    // Tool handlers for AI agent interactions
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      this.logger.info('MCP: Listing available tools', { tenantId: this.tenantId });
      
      return {
        tools: [
          {
            name: 'query_capsules',
            description: 'Query agent capsules with behavioral guarantees',
            inputSchema: {
              type: 'object',
              properties: {
                filter: {
                  type: 'object',
                  properties: {
                    status: { type: 'string', enum: ['active', 'paused', 'terminated'] },
                    tags: { type: 'array', items: { type: 'string' } },
                    behaviorHash: { type: 'string' }
                  }
                },
                limit: { type: 'number', default: 10 }
              }
            }
          },
          {
            name: 'verify_behavior_guarantee',
            description: 'Verify formal behavioral guarantees for an agent',
            inputSchema: {
              type: 'object',
              properties: {
                capsuleId: { type: 'string' },
                behaviorSpec: { type: 'string' },
                proofType: { type: 'string', enum: ['lean', 'marabou', 'dryvr'] }
              },
              required: ['capsuleId', 'behaviorSpec']
            }
          },
          {
            name: 'log_audit_event',
            description: 'Record audit events for compliance and transparency',
            inputSchema: {
              type: 'object',
              properties: {
                eventType: { type: 'string' },
                agentId: { type: 'string' },
                details: { type: 'object' },
                severity: { type: 'string', enum: ['info', 'warning', 'error', 'critical'] }
              },
              required: ['eventType', 'agentId', 'details']
            }
          }
        ]
      };
    });

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;
      
      this.logger.info('MCP: Tool call received', { 
        tool: name, 
        tenantId: this.tenantId,
        args: JSON.stringify(args)
      });

      try {
        switch (name) {
          case 'query_capsules':
            return await this.handleQueryCapsules(args);
          
          case 'verify_behavior_guarantee':
            return await this.handleVerifyBehaviorGuarantee(args);
            
          case 'log_audit_event':
            return await this.handleLogAuditEvent(args);
            
          default:
            throw new McpError(
              ErrorCode.MethodNotFound,
              `Unknown tool: ${name}`
            );
        }
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('MCP: Tool execution failed', { 
          tool: name, 
          error: errorMessage,
          tenantId: this.tenantId 
        });
        
        if (error instanceof McpError) {
          throw error;
        }
        
        throw new McpError(
          ErrorCode.InternalError,
          `Tool execution failed: ${errorMessage}`
        );
      }
    });

    // Resource handlers for agent specification access
    this.server.setRequestHandler(ListResourcesRequestSchema, async () => {
      this.logger.info('MCP: Listing available resources', { tenantId: this.tenantId });
      
      return {
        resources: [
          {
            uri: 'provability://capsules/active',
            name: 'Active Agent Capsules',
            description: 'Currently running agent capsules with behavioral guarantees',
            mimeType: 'application/json'
          },
          {
            uri: 'provability://proofs/lean',
            name: 'Lean Behavioral Proofs',
            description: 'Formal verification proofs in Lean 4',
            mimeType: 'text/plain'
          },
          {
            uri: 'provability://audit/events',
            name: 'Audit Trail',
            description: 'Comprehensive audit events for compliance',
            mimeType: 'application/json'
          }
        ]
      };
    });

    this.server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
      const { uri } = request.params;
      
      this.logger.info('MCP: Resource read requested', { 
        uri, 
        tenantId: this.tenantId 
      });

      try {
        switch (uri) {
          case 'provability://capsules/active':
            return await this.readActiveCapsules();
            
          case 'provability://proofs/lean':
            return await this.readLeanProofs();
            
          case 'provability://audit/events':
            return await this.readAuditEvents();
            
          default:
            throw new McpError(
              ErrorCode.InvalidRequest,
              `Unknown resource URI: ${uri}`
            );
        }
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('MCP: Resource read failed', { 
          uri, 
          error: errorMessage,
          tenantId: this.tenantId 
        });
        
        if (error instanceof McpError) {
          throw error;
        }
        
        throw new McpError(
          ErrorCode.InternalError,
          `Resource read failed: ${errorMessage}`
        );
      }
    });
  }

  private async handleQueryCapsules(args: any) {
    const { filter = {}, limit = 10 } = args;
    
    // Apply tenant isolation if configured
    const whereClause: any = {};
    if (this.tenantId) {
      whereClause.tenantId = this.tenantId;
    }
    
    // Apply user filters
    if (filter.status) {
      whereClause.status = filter.status;
    }
    
    if (filter.behaviorHash) {
      whereClause.behaviorHash = filter.behaviorHash;
    }

    const capsules = await this.prisma.capsule.findMany({
      where: whereClause,
      take: limit,
              select: {
          id: true,
          hash: true,
          specSig: true,
          riskScore: true,
          reason: true,
          createdAt: true,
          tenantId: true
        }
    });

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            capsules: capsules.map(capsule => ({
              id: capsule.id,
              hash: capsule.hash,
              specSig: capsule.specSig,
              riskScore: capsule.riskScore,
              reason: capsule.reason,
              createdAt: capsule.createdAt,
              tenantId: capsule.tenantId
            })),
            total: capsules.length,
            tenantId: this.tenantId
          }, null, 2)
        }
      ]
    };
  }

  private async handleVerifyBehaviorGuarantee(args: any) {
    const { capsuleId, behaviorSpec, proofType = 'lean' } = args;
    
    // Verify capsule exists and tenant access
    const whereClause: any = { id: capsuleId };
    if (this.tenantId) {
      whereClause.tenantId = this.tenantId;
    }
    
    const capsule = await this.prisma.capsule.findFirst({
      where: whereClause
    });
    
    if (!capsule) {
      throw new McpError(
        ErrorCode.InvalidRequest,
        `Capsule not found or access denied: ${capsuleId}`
      );
    }

    // Mock verification result (integrate with actual proof engines)
    const verificationResult = {
      capsuleId,
      behaviorSpec,
      proofType,
      verified: true,
      proofHash: 'proof_' + Math.random().toString(36).substr(2, 9),
      timestamp: new Date().toISOString(),
      constraints: [
        'privacy_budget <= 1.0',
        'output_rate <= 10req/sec',
        'memory_usage <= 512MB'
      ]
    };

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(verificationResult, null, 2)
        }
      ]
    };
  }

  private async handleLogAuditEvent(args: any) {
    const { eventType, agentId, details, severity = 'info' } = args;
    
    const auditEvent = {
      id: 'audit_' + Math.random().toString(36).substr(2, 9),
      eventType,
      agentId,
      details,
      severity,
      timestamp: new Date().toISOString(),
      tenantId: this.tenantId
    };

    // In production, this would store to audit database
    this.logger.info('MCP: Audit event logged', auditEvent);

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            eventId: auditEvent.id,
            message: 'Audit event logged successfully'
          }, null, 2)
        }
      ]
    };
  }

  private async readActiveCapsules() {
    const whereClause: any = {};
    if (this.tenantId) {
      whereClause.tenantId = this.tenantId;
    }
    // Note: Remove status filter as Capsule model doesn't have status field

    const capsules = await this.prisma.capsule.findMany({
      where: whereClause,
      select: {
        id: true,
        hash: true,
        specSig: true,
        riskScore: true
      }
    });

    return {
      contents: [
        {
          type: 'text',
          text: JSON.stringify({ activeCapsules: capsules }, null, 2)
        }
      ]
    };
  }

  private async readLeanProofs() {
    // Mock Lean proof content (integrate with actual proof storage)
    const proofContent = `-- Behavioral Guarantee Proof
theorem agent_behavior_bounded (agent : Agent) :
  ∀ (input : Input), privacy_budget (agent.process input) ≤ 1.0 ∧
                     response_time (agent.process input) ≤ 5000 :=
by
  intro input
  constructor
  · -- Privacy budget proof
    apply privacy_bound_lemma
  · -- Response time proof  
    apply response_time_bound_lemma`;

    return {
      contents: [
        {
          type: 'text',
          text: proofContent
        }
      ]
    };
  }

  private async readAuditEvents() {
    // Mock audit events (integrate with actual audit storage)
    const events = [
      {
        id: 'audit_001',
        eventType: 'agent_deployment',
        agentId: 'agent_123',
        timestamp: new Date().toISOString(),
        details: { version: '1.0.0', behavioral_hash: 'abc123' }
      },
      {
        id: 'audit_002', 
        eventType: 'constraint_violation',
        agentId: 'agent_456',
        timestamp: new Date().toISOString(),
        details: { constraint: 'privacy_budget', violated_value: 1.2 }
      }
    ];

    return {
      contents: [
        {
          type: 'text',
          text: JSON.stringify({ auditEvents: events }, null, 2)
        }
      ]
    };
  }

  async start(): Promise<void> {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    this.logger.info('MCP: Provability-Fabric MCP server started', { 
      tenantId: this.tenantId 
    });
  }

  async stop(): Promise<void> {
    await this.server.close();
    this.logger.info('MCP: Provability-Fabric MCP server stopped', { 
      tenantId: this.tenantId 
    });
  }
}

export default ProvabilityFabricMcpServer;
