// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import WebSocket, { WebSocketServer } from 'ws';
import jwt from 'jsonwebtoken';
import { URL } from 'url';

// WebSocket server configuration
const JWT_SECRET = process.env.JWT_SECRET || 'provability-fabric-dev-secret-2025';
const WS_PORT = process.env.WS_PORT || 8081;

class ProvabilityWebSocketServer {
  constructor() {
    this.wss = null;
    this.clients = new Map(); // Store authenticated clients
    this.rooms = new Map(); // Room-based messaging
    this.metrics = {
      connections: 0,
      messagesTotal: 0,
      broadcastsTotal: 0
    };
  }

  initialize() {
    this.wss = new WebSocketServer({ 
      port: WS_PORT,
      verifyClient: this.verifyClient.bind(this)
    });

    this.wss.on('connection', this.handleConnection.bind(this));
    this.setupHeartbeat();
    
    console.log(`🔗 WebSocket server running on port ${WS_PORT}`);
    console.log(`🔐 Authentication: JWT-based`);
    console.log(`📊 Metrics endpoint: ws://localhost:${WS_PORT}/metrics`);
  }

  // Verify client authentication during connection
  verifyClient(info) {
    try {
      const url = new URL(info.req.url, `http://${info.req.headers.host}`);
      const token = url.searchParams.get('token');
      
      if (!token) {
        console.log('❌ WebSocket connection denied: No token provided');
        return false;
      }

      // Verify JWT token
      const decoded = jwt.verify(token, JWT_SECRET);
      info.req.user = decoded;
      
      console.log(`✅ WebSocket authentication successful: ${decoded.userId || 'anonymous'}`);
      return true;
    } catch (error) {
      console.log(`❌ WebSocket authentication failed: ${error.message}`);
      return false;
    }
  }

  handleConnection(ws, req) {
    const user = req.user;
    const clientId = this.generateClientId();
    
    // Store client with metadata
    this.clients.set(clientId, {
      ws,
      user,
      connectedAt: new Date(),
      lastPing: Date.now(),
      rooms: new Set()
    });

    this.metrics.connections++;
    
    console.log(`🔗 New WebSocket connection: ${clientId} (User: ${user.userId || 'anonymous'})`);

    // Send welcome message
    this.sendToClient(clientId, {
      type: 'connection',
      status: 'connected',
      clientId,
      timestamp: new Date().toISOString(),
      server: 'Provability-Fabric WebSocket v1.0'
    });

    // Setup message handling
    ws.on('message', (data) => this.handleMessage(clientId, data));
    ws.on('close', () => this.handleDisconnection(clientId));
    ws.on('error', (error) => this.handleError(clientId, error));
    ws.on('pong', () => this.handlePong(clientId));

    // Join default room based on user role
    const defaultRoom = user.role || 'general';
    this.joinRoom(clientId, defaultRoom);

    // Send initial system status
    this.sendSystemStatus(clientId);
  }

  handleMessage(clientId, rawData) {
    try {
      const client = this.clients.get(clientId);
      if (!client) return;

      const message = JSON.parse(rawData.toString());
      this.metrics.messagesTotal++;

      console.log(`📨 Message from ${clientId}:`, message.type);

      switch (message.type) {
        case 'ping':
          this.sendToClient(clientId, { type: 'pong', timestamp: new Date().toISOString() });
          break;

        case 'subscribe':
          this.handleSubscription(clientId, message);
          break;

        case 'unsubscribe':
          this.handleUnsubscription(clientId, message);
          break;

        case 'broadcast':
          this.handleBroadcast(clientId, message);
          break;

        case 'join_room':
          this.joinRoom(clientId, message.room);
          break;

        case 'leave_room':
          this.leaveRoom(clientId, message.room);
          break;

        case 'get_metrics':
          this.sendMetrics(clientId);
          break;

        default:
          this.sendToClient(clientId, {
            type: 'error',
            message: `Unknown message type: ${message.type}`
          });
      }
    } catch (error) {
      console.error(`❌ Error processing message from ${clientId}:`, error);
      this.sendToClient(clientId, {
        type: 'error',
        message: 'Invalid message format'
      });
    }
  }

  handleSubscription(clientId, message) {
    const { channel } = message;
    const client = this.clients.get(clientId);
    
    if (!client) return;

    // Add to subscription list
    if (!client.subscriptions) client.subscriptions = new Set();
    client.subscriptions.add(channel);

    this.sendToClient(clientId, {
      type: 'subscription_confirmed',
      channel,
      timestamp: new Date().toISOString()
    });

    console.log(`📺 Client ${clientId} subscribed to ${channel}`);
  }

  handleBroadcast(clientId, message) {
    const client = this.clients.get(clientId);
    if (!client) return;

    // Check permissions (basic role-based)
    if (client.user.role !== 'admin' && client.user.role !== 'moderator') {
      this.sendToClient(clientId, {
        type: 'error',
        message: 'Insufficient permissions for broadcasting'
      });
      return;
    }

    const broadcastMessage = {
      type: 'broadcast',
      from: client.user.userId || 'system',
      content: message.content,
      timestamp: new Date().toISOString()
    };

    this.broadcastToRoom(message.room || 'general', broadcastMessage);
    this.metrics.broadcastsTotal++;
  }

  joinRoom(clientId, roomName) {
    const client = this.clients.get(clientId);
    if (!client) return;

    // Add to room
    if (!this.rooms.has(roomName)) {
      this.rooms.set(roomName, new Set());
    }
    this.rooms.get(roomName).add(clientId);
    client.rooms.add(roomName);

    this.sendToClient(clientId, {
      type: 'room_joined',
      room: roomName,
      timestamp: new Date().toISOString()
    });

    console.log(`🏠 Client ${clientId} joined room: ${roomName}`);
  }

  leaveRoom(clientId, roomName) {
    const client = this.clients.get(clientId);
    if (!client) return;

    if (this.rooms.has(roomName)) {
      this.rooms.get(roomName).delete(clientId);
      if (this.rooms.get(roomName).size === 0) {
        this.rooms.delete(roomName);
      }
    }
    client.rooms.delete(roomName);

    this.sendToClient(clientId, {
      type: 'room_left',
      room: roomName,
      timestamp: new Date().toISOString()
    });
  }

  sendToClient(clientId, message) {
    const client = this.clients.get(clientId);
    if (client && client.ws.readyState === WebSocket.OPEN) {
      client.ws.send(JSON.stringify(message));
      return true;
    }
    return false;
  }

  broadcastToRoom(roomName, message) {
    const room = this.rooms.get(roomName);
    if (!room) return 0;

    let sentCount = 0;
    room.forEach(clientId => {
      if (this.sendToClient(clientId, message)) {
        sentCount++;
      }
    });

    console.log(`📡 Broadcast to room ${roomName}: ${sentCount} clients`);
    return sentCount;
  }

  broadcastToAll(message) {
    let sentCount = 0;
    this.clients.forEach((client, clientId) => {
      if (this.sendToClient(clientId, message)) {
        sentCount++;
      }
    });
    return sentCount;
  }

  sendSystemStatus(clientId) {
    const status = {
      type: 'system_status',
      services: {
        admin: this.checkServiceHealth('http://localhost:9000'),
        marketplace: this.checkServiceHealth('http://localhost:3000'),
        api: this.checkServiceHealth('http://localhost:8080'),
        docs: this.checkServiceHealth('http://127.0.0.1:8002')
      },
      timestamp: new Date().toISOString()
    };

    this.sendToClient(clientId, status);
  }

  sendMetrics(clientId) {
    const metrics = {
      type: 'metrics',
      data: {
        ...this.metrics,
        activeConnections: this.clients.size,
        activeRooms: this.rooms.size,
        uptime: process.uptime(),
        memory: process.memoryUsage()
      },
      timestamp: new Date().toISOString()
    };

    this.sendToClient(clientId, metrics);
  }

  async checkServiceHealth(url) {
    try {
      const response = await fetch(url, { method: 'HEAD' });
      return response.ok ? 'online' : 'offline';
    } catch {
      return 'offline';
    }
  }

  handleDisconnection(clientId) {
    const client = this.clients.get(clientId);
    if (client) {
      // Remove from all rooms
      client.rooms.forEach(roomName => {
        this.leaveRoom(clientId, roomName);
      });
      
      this.clients.delete(clientId);
      this.metrics.connections--;
      
      console.log(`🔌 Client disconnected: ${clientId}`);
    }
  }

  handleError(clientId, error) {
    console.error(`❌ WebSocket error for client ${clientId}:`, error);
  }

  handlePong(clientId) {
    const client = this.clients.get(clientId);
    if (client) {
      client.lastPing = Date.now();
    }
  }

  setupHeartbeat() {
    setInterval(() => {
      const now = Date.now();
      this.clients.forEach((client, clientId) => {
        if (client.ws.readyState === WebSocket.OPEN) {
          // Check if client is still responsive
          if (now - client.lastPing > 60000) { // 60 seconds timeout
            console.log(`💔 Heartbeat timeout for client ${clientId}`);
            client.ws.terminate();
          } else {
            client.ws.ping();
          }
        } else {
          this.handleDisconnection(clientId);
        }
      });
    }, 30000); // Check every 30 seconds
  }

  generateClientId() {
    return `client_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }

  // Public API methods for integration
  notifyServiceStatus(serviceName, status) {
    this.broadcastToAll({
      type: 'service_status_update',
      service: serviceName,
      status,
      timestamp: new Date().toISOString()
    });
  }

  notifyNewPackage(packageData) {
    this.broadcastToRoom('marketplace', {
      type: 'new_package',
      package: packageData,
      timestamp: new Date().toISOString()
    });
  }

  notifySystemAlert(level, message) {
    this.broadcastToRoom('admin', {
      type: 'system_alert',
      level,
      message,
      timestamp: new Date().toISOString()
    });
  }
}

// Create and export singleton instance
const wsServer = new ProvabilityWebSocketServer();

export { wsServer };
export default ProvabilityWebSocketServer;
