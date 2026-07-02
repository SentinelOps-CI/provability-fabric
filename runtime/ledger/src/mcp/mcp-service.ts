/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * MCP Service Manager for Provability-Fabric
 * Coordinates MCP server and proxy components with existing infrastructure
 */

import { Router } from 'express';
import { PrismaClient } from '@prisma/client';
import winston from 'winston';
import { WebSocketServer, WebSocket, type RawData } from 'ws';
import type { Server as HttpServer } from 'http';
import type { IncomingMessage } from 'http';
import ProvabilityFabricMcpServer from './mcp-server.js';
import McpProxy from './mcp-proxy.js';
import type { JsonRpcRequest, JsonRpcResponse, McpServiceMetrics, McpWebSocketMessage } from './types.js';
import type { McpAuthenticatedRequest } from '../types/express-mcp.js';

interface McpServiceConfig {
  name: string;
  version: string;
  description: string;
  enableWebSocket: boolean;
  sidecarUrl: string;
  enableMultiTenant: boolean;
}

/** Canonical tenant claim: `tid` preferred; legacy `tenantId` / `tenant_id` accepted. */
function resolveTenantId(user: {
  tid?: string;
  tenantId?: string;
  tenant_id?: string;
} | undefined): string | undefined {
  if (!user) return undefined;
  return user.tid ?? user.tenantId ?? user.tenant_id;
}

export class McpService {
  private config: McpServiceConfig;
  private prisma: PrismaClient;
  private logger: winston.Logger;
  private mcpServers: Map<string, ProvabilityFabricMcpServer> = new Map();
  private mcpProxy: McpProxy;
  private wsServer?: WebSocketServer;
  private router: Router;

  constructor(
    config: McpServiceConfig,
    prisma: PrismaClient,
    logger: winston.Logger
  ) {
    this.config = config;
    this.prisma = prisma;
    this.logger = logger;
    this.mcpProxy = new McpProxy(prisma, logger, config.sidecarUrl);
    this.router = Router();
    this.setupRoutes();
  }

  /**
   * Initialize MCP service with multi-tenant support
   */
  async initialize(): Promise<void> {
    this.logger.info('MCP: Initializing Provability-Fabric MCP Service', {
      config: this.config
    });

    if (this.config.enableMultiTenant) {
      await this.initializeMultiTenantServers();
    } else {
      await this.initializeSingleTenantServer();
    }

    this.logger.info('MCP: Service initialization complete');
  }

  /**
   * Setup Express routes for MCP endpoints
   */
  private setupRoutes(): void {
    // Apply MCP proxy middleware for all MCP routes
    this.router.use('/mcp', this.mcpProxy.middleware());

    // MCP JSON-RPC endpoint
    this.router.post('/mcp/jsonrpc', async (req, res) => {
      try {
        const mcpReq = req as McpAuthenticatedRequest;
        const mcpContext = mcpReq.mcpContext;
        const tenantId = mcpContext?.tenantId;

        // Get or create tenant-specific MCP server
        const mcpServer = await this.getMcpServer(tenantId);
        
        // Forward request to appropriate MCP server
        const response = await this.forwardToMcpServer(mcpServer, req.body);
        
        res.json(response);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        const errorStack = error instanceof Error ? error.stack : undefined;
        this.logger.error('MCP: JSON-RPC endpoint error', {
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
    });

    // MCP server discovery endpoint
    this.router.get('/mcp/servers', async (req, res) => {
      try {
        const tenantId = resolveTenantId((req as McpAuthenticatedRequest).user);

        const servers = Array.from(this.mcpServers.entries()).map(([id, server]) => ({
          id,
          name: this.config.name,
          version: this.config.version,
          description: this.config.description,
          tenantId: id === 'default' ? null : id,
          capabilities: ['tools', 'resources']
        }));

        res.json({
          servers: tenantId ? servers.filter(s => s.tenantId === tenantId || s.tenantId === null) : servers
        });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('MCP: Server discovery error', { error: errorMessage });
        res.status(500).json({ error: 'Failed to discover MCP servers' });
      }
    });

    // MCP proxy statistics endpoint
    this.router.get('/mcp/stats', async (req, res) => {
      try {
        const tenantId = resolveTenantId((req as McpAuthenticatedRequest).user);
        const stats = await this.mcpProxy.getStats(tenantId);
        res.json(stats);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('MCP: Stats endpoint error', { error: errorMessage });
        res.status(500).json({ error: 'Failed to get MCP statistics' });
      }
    });

    // Health check endpoint
    this.router.get('/mcp/health', (req, res) => {
      const health = {
        status: 'healthy',
        servers: this.mcpServers.size,
        timestamp: new Date().toISOString(),
        version: this.config.version
      };
      res.json(health);
    });
  }

  /**
   * Initialize single-tenant MCP server
   */
  private async initializeSingleTenantServer(): Promise<void> {
    const mcpServer = new ProvabilityFabricMcpServer(
      {
        name: this.config.name,
        version: this.config.version,
        description: this.config.description
      },
      this.prisma,
      this.logger
    );

    this.mcpServers.set('default', mcpServer);
    this.logger.info('MCP: Single-tenant server initialized');
  }

  /**
   * Initialize multi-tenant MCP servers
   */
  private async initializeMultiTenantServers(): Promise<void> {
    // Initialize default server for non-tenant requests
    await this.initializeSingleTenantServer();

    // Pre-initialize servers for active tenants
    const activeTenants = await this.prisma.tenant.findMany({
      where: { 
        // Add conditions for active tenants
      },
      select: { id: true, name: true }
    });

    for (const tenant of activeTenants) {
      await this.createTenantMcpServer(tenant.id);
    }

    this.logger.info('MCP: Multi-tenant servers initialized', {
      tenants: activeTenants.length
    });
  }

  /**
   * Create or get MCP server for specific tenant
   */
  private async getMcpServer(tenantId?: string): Promise<ProvabilityFabricMcpServer> {
    const serverId = tenantId || 'default';
    
    if (!this.mcpServers.has(serverId)) {
      if (tenantId) {
        await this.createTenantMcpServer(tenantId);
      } else {
        throw new Error('Default MCP server not initialized');
      }
    }

    return this.mcpServers.get(serverId)!;
  }

  /**
   * Create MCP server for specific tenant
   */
  private async createTenantMcpServer(tenantId: string): Promise<void> {
    const mcpServer = new ProvabilityFabricMcpServer(
      {
        name: `${this.config.name}-${tenantId}`,
        version: this.config.version,
        description: `${this.config.description} (Tenant: ${tenantId})`,
        tenantId
      },
      this.prisma,
      this.logger
    );

    this.mcpServers.set(tenantId, mcpServer);
    
    this.logger.info('MCP: Tenant server created', { tenantId });
  }

  /**
   * Forward request to MCP server and handle response
   */
  private async forwardToMcpServer(
    mcpServer: ProvabilityFabricMcpServer,
    request: JsonRpcRequest
  ): Promise<JsonRpcResponse> {
    if (!request?.method) {
      return {
        jsonrpc: '2.0',
        error: { code: -32600, message: 'Invalid request: missing method' },
        id: request?.id,
      };
    }

    const handler = (mcpServer as ProvabilityFabricMcpServer & {
      handleRequest?: (req: JsonRpcRequest) => Promise<JsonRpcResponse>;
    }).handleRequest;
    if (typeof handler === 'function') {
      try {
        return await handler.call(mcpServer, request);
      } catch (error) {
        return {
          jsonrpc: '2.0',
          error: {
            code: -32603,
            message: error instanceof Error ? error.message : 'Unknown error',
          },
          id: request.id,
        };
      }
    }

    return {
      jsonrpc: '2.0',
      error: {
        code: 501,
        message: 'MCP backend not configured for this method',
      },
      id: request.id,
    };
  }

  /**
   * Setup WebSocket support for real-time MCP events
   */
  setupWebSocket(server: HttpServer): void {
    if (!this.config.enableWebSocket) {
      return;
    }

    this.wsServer = new WebSocketServer({ 
      server,
      path: '/mcp/ws'
    });

    this.wsServer.on('connection', (ws: WebSocket, req: IncomingMessage) => {
      this.logger.info('MCP: WebSocket connection established', { path: req.url });
      
      ws.on('message', async (data: RawData) => {
        try {
          const message = JSON.parse(data.toString()) as McpWebSocketMessage;
          
          // Handle real-time MCP events
          switch (message.type) {
            case 'subscribe':
              await this.handleSubscription(ws, message);
              break;
              
            case 'mcp_request':
              await this.handleRealTimeMcpRequest(ws, message);
              break;
              
            default:
              ws.send(JSON.stringify({
                type: 'error',
                message: 'Unknown message type',
                timestamp: new Date().toISOString()
              }));
          }
        } catch (error) {
          const errorMessage = error instanceof Error ? error.message : 'Unknown error';
          this.logger.error('MCP: WebSocket message error', { error: errorMessage });
          ws.send(JSON.stringify({
            type: 'error',
            message: 'Failed to process message',
            timestamp: new Date().toISOString()
          }));
        }
      });

      ws.on('close', () => {
        this.logger.info('MCP: WebSocket connection closed');
      });
    });

    this.logger.info('MCP: WebSocket server configured');
  }

  /**
   * Handle WebSocket subscription requests
   */
  private async handleSubscription(ws: WebSocket, message: McpWebSocketMessage): Promise<void> {
    const { tenantId, eventTypes } = message;
    
    // Store subscription info (implement proper subscription management)
    this.logger.info('MCP: WebSocket subscription', { tenantId, eventTypes });
    
    ws.send(JSON.stringify({
      type: 'subscription_confirmed',
      tenantId,
      eventTypes,
      timestamp: new Date().toISOString()
    }));
  }

  /**
   * Handle real-time MCP requests via WebSocket
   */
  private async handleRealTimeMcpRequest(ws: WebSocket, message: McpWebSocketMessage): Promise<void> {
    const { mcpRequest, tenantId } = message;
    
    try {
      if (!mcpRequest) {
        throw new Error('Missing mcpRequest in WebSocket message');
      }
      const mcpServer = await this.getMcpServer(tenantId);
      const response = await this.forwardToMcpServer(mcpServer, mcpRequest);
      
      ws.send(JSON.stringify({
        type: 'mcp_response',
        response,
        timestamp: new Date().toISOString()
      }));
    } catch (error) {
      ws.send(JSON.stringify({
        type: 'error',
        message: 'Failed to process MCP request',
        error: error instanceof Error ? error.message : 'Unknown error',
        timestamp: new Date().toISOString()
      }));
    }
  }

  /**
   * Broadcast MCP events to subscribed WebSocket clients
   */
  broadcastEvent(event: {
    type: string;
    tenantId?: string;
    data: unknown;
  }): void {
    if (!this.wsServer) {
      return;
    }

    const message = JSON.stringify({
      type: 'mcp_event',
      event,
      timestamp: new Date().toISOString()
    });

    this.wsServer.clients.forEach((client) => {
      const wsClient = client as WebSocket;
      if (wsClient.readyState === WebSocket.OPEN) {
        wsClient.send(message);
      }
    });
  }

  /**
   * Get Express router for MCP endpoints
   */
  getRouter(): Router {
    return this.router;
  }

  /**
   * Shutdown MCP service gracefully
   */
  async shutdown(): Promise<void> {
    this.logger.info('MCP: Shutting down service');

    // Stop all MCP servers
    for (const [tenantId, mcpServer] of this.mcpServers) {
      try {
        await mcpServer.stop();
        this.logger.info('MCP: Server stopped', { tenantId });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('MCP: Error stopping server', { 
          tenantId, 
          error: errorMessage 
        });
      }
    }

    // Close WebSocket server
    if (this.wsServer) {
      this.wsServer.close();
      this.logger.info('MCP: WebSocket server closed');
    }

    this.logger.info('MCP: Service shutdown complete');
  }

  /**
   * Get service metrics for monitoring
   */
  getMetrics(): McpServiceMetrics {
    return {
      servers: this.mcpServers.size,
      connections: this.wsServer?.clients?.size || 0,
      uptime: process.uptime(),
      timestamp: new Date().toISOString()
    };
  }
}

export default McpService;
