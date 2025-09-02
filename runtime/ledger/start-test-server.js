/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Test Server Startup Script
 * Starts a minimal server for MCP integration testing
 */

const express = require('express');
const cors = require('cors');
const { WebSocketServer } = require('ws');
const http = require('http');

// Simplified mock server for testing MCP endpoints
class TestMcpServer {
  constructor(port = 4000) {
    this.port = port;
    this.app = express();
    this.server = null;
    this.wsServer = null;
    
    this.setupMiddleware();
    this.setupRoutes();
    this.setupWebSocket();
  }

  setupMiddleware() {
    this.app.use(cors());
    this.app.use(express.json());
    
    // Simple auth middleware for testing
    this.app.use((req, res, next) => {
      const authHeader = req.headers.authorization;
      if (authHeader && authHeader.startsWith('Bearer ')) {
        req.user = {
          tenant_id: 'test-tenant',
          sub: 'test-user'
        };
      }
      next();
    });
  }

  setupRoutes() {
    // Health check
    this.app.get('/health', (req, res) => {
      res.json({ 
        status: 'healthy', 
        timestamp: new Date().toISOString(),
        service: 'test-mcp-server'
      });
    });

    // MCP Health check
    this.app.get('/api/mcp/health', (req, res) => {
      res.json({
        status: 'healthy',
        servers: 1,
        timestamp: new Date().toISOString(),
        version: '1.0.0-test'
      });
    });

    // MCP Server discovery
    this.app.get('/api/mcp/servers', (req, res) => {
      res.json({
        servers: [
          {
            id: 'test-server',
            name: 'provability-fabric-mcp-test',
            version: '1.0.0',
            description: 'Test MCP server for integration testing',
            tenantId: req.user?.tenant_id || null,
            capabilities: ['tools', 'resources']
          }
        ]
      });
    });

    // MCP Statistics
    this.app.get('/api/mcp/stats', (req, res) => {
      res.json({
        totalRequests: 42,
        blockedRequests: 2,
        averageResponseTime: 150,
        tenantId: req.user?.tenant_id,
        timestamp: new Date().toISOString()
      });
    });

    // MCP JSON-RPC endpoint
    this.app.post('/api/mcp/jsonrpc', (req, res) => {
      const { jsonrpc, method, params, id } = req.body;

      // Validate JSON-RPC format
      if (jsonrpc !== '2.0') {
        return res.status(500).json({
          jsonrpc: '2.0',
          error: {
            code: -32600,
            message: 'Invalid Request'
          },
          id
        });
      }

      if (!method) {
        return res.status(500).json({
          jsonrpc: '2.0',
          error: {
            code: -32600,
            message: 'Missing method'
          },
          id
        });
      }

      // Simulate policy enforcement
      if (method === 'tools/call' && params?.arguments?.limit > 1000) {
        return res.status(403).json({
          jsonrpc: '2.0',
          error: {
            code: -32000,
            message: 'Policy violation',
            data: {
              reason: 'Query limit too high',
              violatedConstraints: ['max_query_limit']
            }
          },
          id
        });
      }

      // Handle different methods
      let result;
      switch (method) {
        case 'tools/list':
          result = {
            tools: [
              {
                name: 'query_capsules',
                description: 'Query agent capsules with behavioral guarantees',
                inputSchema: {
                  type: 'object',
                  properties: {
                    filter: { type: 'object' },
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
          break;

        case 'tools/call':
          const { name, arguments: args } = params;
          
          switch (name) {
            case 'query_capsules':
              result = {
                content: [
                  {
                    type: 'text',
                    text: JSON.stringify({
                      capsules: [
                        {
                          id: 'test-capsule-001',
                          hash: 'sha256:abcd1234',
                          specSig: 'spec-signature-001',
                          riskScore: 0.75,
                          reason: 'Test capsule for MCP integration',
                          tenantId: req.user?.tenant_id
                        }
                      ],
                      total: 1,
                      tenantId: req.user?.tenant_id
                    }, null, 2)
                  }
                ]
              };
              break;

            case 'verify_behavior_guarantee':
              result = {
                content: [
                  {
                    type: 'text',
                    text: JSON.stringify({
                      capsuleId: args.capsuleId,
                      behaviorSpec: args.behaviorSpec,
                      proofType: args.proofType || 'lean',
                      verified: true,
                      proofHash: 'proof_' + Math.random().toString(36).substr(2, 9),
                      timestamp: new Date().toISOString(),
                      constraints: [
                        'privacy_budget <= 1.0',
                        'output_rate <= 10req/sec',
                        'memory_usage <= 512MB'
                      ]
                    }, null, 2)
                  }
                ]
              };
              break;

            case 'log_audit_event':
              result = {
                content: [
                  {
                    type: 'text',
                    text: JSON.stringify({
                      success: true,
                      eventId: 'audit_' + Math.random().toString(36).substr(2, 9),
                      message: 'Audit event logged successfully'
                    }, null, 2)
                  }
                ]
              };
              break;

            default:
              return res.status(500).json({
                jsonrpc: '2.0',
                error: {
                  code: -32601,
                  message: `Unknown tool: ${name}`
                },
                id
              });
          }
          break;

        case 'resources/list':
          result = {
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
              }
            ]
          };
          break;

        case 'resources/read':
          const { uri } = params;
          
          if (uri === 'provability://capsules/active') {
            result = {
              contents: [
                {
                  type: 'text',
                  text: JSON.stringify({
                    activeCapsules: [
                      {
                        id: 'test-capsule-001',
                        hash: 'sha256:abcd1234',
                        specSig: 'spec-signature-001',
                        riskScore: 0.75
                      }
                    ]
                  }, null, 2)
                }
              ]
            };
          } else if (!uri.startsWith('provability://')) {
            return res.status(403).json({
              jsonrpc: '2.0',
              error: {
                code: -32000,
                message: 'Policy violation',
                data: {
                  reason: 'Unauthorized resource URI',
                  violatedConstraints: ['allowed_uri_patterns']
                }
              },
              id
            });
          } else {
            return res.status(500).json({
              jsonrpc: '2.0',
              error: {
                code: -32601,
                message: `Unknown resource URI: ${uri}`
              },
              id
            });
          }
          break;

        default:
          return res.status(500).json({
            jsonrpc: '2.0',
            error: {
              code: -32601,
              message: `Method not found: ${method}`
            },
            id
          });
      }

      res.json({
        jsonrpc: '2.0',
        result,
        id
      });
    });

    // Mock other endpoints
    this.app.post('/usage', (req, res) => {
      res.json({ message: 'Usage recorded', timestamp: new Date().toISOString() });
    });

    this.app.post('/graphql', (req, res) => {
      res.json({ 
        data: { 
          __schema: { 
            types: [
              { name: 'Query' },
              { name: 'Mutation' },
              { name: 'Tenant' },
              { name: 'Capsule' }
            ] 
          } 
        } 
      });
    });
  }

  setupWebSocket() {
    // WebSocket will be setup when server starts
  }

  start() {
    return new Promise((resolve, reject) => {
      this.server = http.createServer(this.app);
      
      // Setup WebSocket server
      this.wsServer = new WebSocketServer({ 
        server: this.server,
        path: '/mcp/ws'
      });

      this.wsServer.on('connection', (ws) => {
        console.log('🔌 WebSocket connection established');
        
        ws.on('message', (data) => {
          try {
            const message = JSON.parse(data.toString());
            console.log('📨 WebSocket message received:', message.type);
            
            switch (message.type) {
              case 'subscribe':
                ws.send(JSON.stringify({
                  type: 'subscription_confirmed',
                  tenantId: message.tenantId,
                  eventTypes: message.eventTypes,
                  timestamp: new Date().toISOString()
                }));
                break;
                
              case 'mcp_request':
                ws.send(JSON.stringify({
                  type: 'mcp_response',
                  response: {
                    jsonrpc: '2.0',
                    result: { message: 'WebSocket MCP request processed' },
                    id: message.mcpRequest?.id
                  },
                  timestamp: new Date().toISOString()
                }));
                break;
                
              default:
                ws.send(JSON.stringify({
                  type: 'error',
                  message: 'Unknown message type',
                  timestamp: new Date().toISOString()
                }));
            }
          } catch (error) {
            ws.send(JSON.stringify({
              type: 'error',
              message: 'Failed to process message',
              timestamp: new Date().toISOString()
            }));
          }
        });

        ws.on('close', () => {
          console.log('🔌 WebSocket connection closed');
        });
      });

      this.server.listen(this.port, (err) => {
        if (err) {
          reject(err);
        } else {
          console.log(`🚀 Test MCP Server ready at http://localhost:${this.port}`);
          console.log(`🤖 MCP endpoints: http://localhost:${this.port}/api/mcp/*`);
          console.log(`🔌 MCP WebSocket: ws://localhost:${this.port}/mcp/ws`);
          resolve();
        }
      });
    });
  }

  stop() {
    return new Promise((resolve) => {
      if (this.wsServer) {
        this.wsServer.close();
      }
      
      if (this.server) {
        this.server.close(() => {
          console.log('✅ Test server stopped');
          resolve();
        });
      } else {
        resolve();
      }
    });
  }
}

// Start server if run directly
if (require.main === module) {
  const server = new TestMcpServer();
  
  server.start().catch(error => {
    console.error('❌ Failed to start test server:', error.message);
    process.exit(1);
  });

  // Graceful shutdown
  process.on('SIGINT', async () => {
    console.log('🛑 Shutting down test server...');
    await server.stop();
    process.exit(0);
  });
}

module.exports = TestMcpServer;
