# WebSocket API Reference

Complete API reference for the Provability-Fabric WebSocket real-time communication system.

## Connection

### Authentication

All WebSocket connections require JWT authentication via query parameter:

```
ws://localhost:8081?token=<jwt-token>
```

**Connection Flow:**
1. Obtain JWT token from `/auth/login` endpoint
2. Connect to WebSocket with token as query parameter
3. Server validates token and establishes authenticated connection
4. Client automatically joins default room based on user role

### Connection Events

| Event | Description | Data |
|-------|-------------|------|
| `open` | Connection established | None |
| `message` | Message received | JSON object |
| `close` | Connection closed | Close code and reason |
| `error` | Connection error | Error object |

## Message Format

All messages use JSON format:

```json
{
  "type": "message_type",
  "timestamp": "2025-01-01T12:00:00.000Z",
  "data": { /* message-specific data */ }
}
```

## Client → Server Messages

### Ping/Pong

**Send Ping:**
```json
{
  "type": "ping"
}
```

**Receive Pong:**
```json
{
  "type": "pong",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

### Room Management

**Join Room:**
```json
{
  "type": "join_room",
  "room": "marketplace"
}
```

**Leave Room:**
```json
{
  "type": "leave_room",
  "room": "marketplace"
}
```

**Available Rooms:**
- `general` - All authenticated users
- `admin` - Admin users only
- `marketplace` - Marketplace events
- `monitoring` - System monitoring data

### Subscriptions

**Subscribe to Channel:**
```json
{
  "type": "subscribe",
  "channel": "package_updates"
}
```

**Unsubscribe from Channel:**
```json
{
  "type": "unsubscribe",
  "channel": "package_updates"
}
```

### Broadcasting (Admin Only)

**Broadcast Message:**
```json
{
  "type": "broadcast",
  "room": "general",
  "content": "System maintenance scheduled for tonight"
}
```

### System Requests

**Get Metrics (Admin Only):**
```json
{
  "type": "get_metrics"
}
```

## Server → Client Messages

### Connection Status

**Connection Confirmed:**
```json
{
  "type": "connection",
  "status": "connected",
  "clientId": "client_1641234567890_abc123def",
  "timestamp": "2025-01-01T12:00:00.000Z",
  "server": "Provability-Fabric WebSocket v1.0"
}
```

**Room Joined:**
```json
{
  "type": "room_joined",
  "room": "marketplace",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

**Room Left:**
```json
{
  "type": "room_left",
  "room": "marketplace",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

### Service Monitoring

**System Status:**
```json
{
  "type": "system_status",
  "services": {
    "admin": "online",
    "marketplace": "online",
    "api": "online",
    "docs": "offline"
  },
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

**Service Status Update:**
```json
{
  "type": "service_status_update",
  "service": "marketplace",
  "status": "online",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

### Marketplace Events

**New Package:**
```json
{
  "type": "new_package",
  "package": {
    "id": "neural-verifier",
    "name": "Neural Network Verifier",
    "version": "1.0.0",
    "author": "Stanford",
    "type": "adapter",
    "description": "Advanced neural network verification tools"
  },
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

**Package Installation:**
```json
{
  "type": "package_installation",
  "installId": "install-1641234567890",
  "packageId": "neural-verifier",
  "version": "1.0.0",
  "tenantId": "acme-corp",
  "userId": "user-123",
  "status": "initiated",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

### System Alerts

**System Alert:**
```json
{
  "type": "system_alert",
  "level": "info",
  "message": "User John Doe logged in",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

**Alert Levels:**
- `info` - Informational messages
- `warn` - Warning conditions
- `error` - Error conditions

### Performance Metrics

**System Metrics (Admin Only):**
```json
{
  "type": "metrics",
  "data": {
    "connections": 15,
    "messagesTotal": 1247,
    "broadcastsTotal": 23,
    "activeConnections": 15,
    "activeRooms": 4,
    "uptime": 86400,
    "memory": {
      "rss": 41943040,
      "heapTotal": 29360128,
      "heapUsed": 20504312,
      "external": 1089118,
      "arrayBuffers": 26182
    }
  },
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

### Error Messages

**Error Response:**
```json
{
  "type": "error",
  "message": "Unknown message type: invalid_type",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

**Permission Error:**
```json
{
  "type": "error",
  "message": "Insufficient permissions for broadcasting",
  "timestamp": "2025-01-01T12:00:00.000Z"
}
```

## Client Libraries

### JavaScript/TypeScript

**React Hook Usage:**
```typescript
import { useWebSocket } from '../hooks/useWebSocket';

const MyComponent = () => {
  const { 
    isConnected, 
    isConnecting, 
    sendMessage, 
    joinRoom,
    leaveRoom,
    lastMessage 
  } = useWebSocket({
    onMessage: (message) => {
      console.log('Received:', message);
    },
    onConnect: () => {
      console.log('Connected to WebSocket');
    },
    onDisconnect: () => {
      console.log('Disconnected from WebSocket');
    }
  });

  return (
    <div>
      <div>Status: {isConnected ? 'Connected' : 'Disconnected'}</div>
      <button onClick={() => joinRoom('marketplace')}>
        Join Marketplace
      </button>
      <button onClick={() => sendMessage({ type: 'ping' })}>
        Send Ping
      </button>
    </div>
  );
};
```

**Direct WebSocket Usage:**
```javascript
// Connect with authentication
const token = localStorage.getItem('authToken');
const ws = new WebSocket(`ws://localhost:8081?token=${token}`);

// Handle connection
ws.onopen = () => {
  console.log('Connected');
  
  // Join a room
  ws.send(JSON.stringify({
    type: 'join_room',
    room: 'marketplace'
  }));
};

// Handle messages
ws.onmessage = (event) => {
  const message = JSON.parse(event.data);
  
  switch (message.type) {
    case 'system_alert':
      showNotification(message.message, message.level);
      break;
    case 'new_package':
      addPackageToUI(message.package);
      break;
    case 'service_status_update':
      updateServiceStatus(message.service, message.status);
      break;
  }
};

// Handle errors
ws.onerror = (error) => {
  console.error('WebSocket error:', error);
};

// Handle close
ws.onclose = (event) => {
  console.log('Disconnected:', event.code, event.reason);
};
```

### Node.js Client

```javascript
const WebSocket = require('ws');

class ProvabilityFabricWSClient {
  constructor(token) {
    this.token = token;
    this.ws = null;
    this.reconnectAttempts = 0;
    this.maxReconnectAttempts = 5;
  }

  connect() {
    const url = `ws://localhost:8081?token=${this.token}`;
    this.ws = new WebSocket(url);

    this.ws.on('open', () => {
      console.log('Connected to Provability-Fabric WebSocket');
      this.reconnectAttempts = 0;
    });

    this.ws.on('message', (data) => {
      const message = JSON.parse(data.toString());
      this.handleMessage(message);
    });

    this.ws.on('close', () => {
      console.log('WebSocket connection closed');
      this.attemptReconnect();
    });

    this.ws.on('error', (error) => {
      console.error('WebSocket error:', error);
    });
  }

  sendMessage(message) {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(message));
    }
  }

  joinRoom(room) {
    this.sendMessage({ type: 'join_room', room });
  }

  leaveRoom(room) {
    this.sendMessage({ type: 'leave_room', room });
  }

  handleMessage(message) {
    console.log('Received message:', message.type, message);
  }

  attemptReconnect() {
    if (this.reconnectAttempts < this.maxReconnectAttempts) {
      this.reconnectAttempts++;
      setTimeout(() => {
        console.log(`Reconnection attempt ${this.reconnectAttempts}`);
        this.connect();
      }, 3000 * this.reconnectAttempts);
    }
  }

  disconnect() {
    if (this.ws) {
      this.ws.close();
    }
  }
}

// Usage
const client = new ProvabilityFabricWSClient('your-jwt-token');
client.connect();
```

## Error Codes

### WebSocket Close Codes

| Code | Description |
|------|-------------|
| 1000 | Normal closure |
| 1001 | Going away |
| 1002 | Protocol error |
| 1003 | Unsupported data |
| 1006 | Abnormal closure |
| 1011 | Server error |
| 1015 | TLS handshake error |

### Custom Error Messages

| Error | Description | Solution |
|-------|-------------|----------|
| "No token provided" | JWT token missing from connection | Include token in query parameter |
| "Invalid or expired token" | JWT token validation failed | Refresh token and reconnect |
| "Unknown message type" | Invalid message type sent | Check message format and type |
| "Insufficient permissions" | User lacks required permissions | Check user role and permissions |

## Rate Limiting

Basic rate limiting is implemented:

- **Connection limit**: 1000 concurrent connections per server
- **Message limit**: No strict limit, but monitoring enabled
- **Room limit**: No limit on room membership

Headers included in response:
```
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1641234567890
```

## Security

### Authentication

- **Required**: JWT token in query parameter
- **Validation**: Token validated on connection establishment
- **Expiration**: Connections closed when token expires

### Authorization

- **Room Access**: Basic room-based permissions
- **Broadcasting**: Admin/moderator roles only
- **Metrics**: Admin role only

### Best Practices

1. **Token Security**: Store tokens securely, rotate regularly
2. **Connection Limits**: Monitor connection counts
3. **Message Validation**: Validate all incoming messages
4. **Error Handling**: Don't expose sensitive information in errors
5. **Logging**: Log authentication attempts and errors

## Testing

### Connection Testing

```bash
# Install wscat for testing
npm install -g wscat

# Test connection
wscat -c "ws://localhost:8081?token=your-jwt-token"

# Send test message
> {"type": "ping"}
< {"type": "pong", "timestamp": "2025-01-01T12:00:00.000Z"}
```

### Automated Testing

```javascript
// Jest test example
const WebSocket = require('ws');

describe('WebSocket API', () => {
  let ws;
  const token = 'valid-jwt-token';

  beforeEach((done) => {
    ws = new WebSocket(`ws://localhost:8081?token=${token}`);
    ws.on('open', done);
  });

  afterEach(() => {
    ws.close();
  });

  test('should receive connection confirmation', (done) => {
    ws.on('message', (data) => {
      const message = JSON.parse(data.toString());
      if (message.type === 'connection') {
        expect(message.status).toBe('connected');
        expect(message.clientId).toBeDefined();
        done();
      }
    });
  });

  test('should handle ping/pong', (done) => {
    ws.send(JSON.stringify({ type: 'ping' }));
    
    ws.on('message', (data) => {
      const message = JSON.parse(data.toString());
      if (message.type === 'pong') {
        expect(message.timestamp).toBeDefined();
        done();
      }
    });
  });
});
```

## Performance

### Connection Management

- **Heartbeat**: 30-second ping/pong cycle
- **Timeout**: 60-second unresponsive connection timeout
- **Cleanup**: Automatic cleanup of dead connections

### Memory Usage

- **Per Connection**: ~1KB metadata per connection
- **Room Storage**: Minimal overhead for room membership
- **Message Buffering**: No message buffering (real-time only)

### Scaling Considerations

For high-traffic deployments:

1. **Load Balancing**: Use sticky sessions for WebSocket connections
2. **Redis Pub/Sub**: For multi-server message broadcasting
3. **Connection Pooling**: Monitor and limit concurrent connections
4. **Health Monitoring**: Regular health checks and metrics collection

## Troubleshooting

### Common Issues

1. **Connection Refused**
   - Check if WebSocket server is running on port 8081
   - Verify firewall settings

2. **Authentication Failed**
   - Verify JWT token is valid and not expired
   - Check token format in connection URL

3. **Messages Not Received**
   - Verify connection is established
   - Check room membership for targeted messages

4. **Frequent Disconnections**
   - Check network stability
   - Verify heartbeat responses

### Debug Commands

```bash
# Check WebSocket server
netstat -an | grep 8081

# Test authentication
curl -H "Authorization: Bearer <token>" http://localhost:8080/auth/profile

# Monitor WebSocket traffic (Linux/macOS)
sudo tcpdump -i any port 8081
```
