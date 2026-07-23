# Production Deployment Guide

> **Historical aspirational web-stack guide.** Canonical deployment: [`docs/guides/deployment-guide.md`](../../guides/deployment-guide.md). Live redirect stub: [`docs/guides/deployment/production-deployment.md`](../../guides/deployment/production-deployment.md).

This guide covers deploying the enhanced Provability-Fabric web services with all the new features including WebSocket real-time communication, advanced search, user authentication, and performance optimizations.

## Overview

The production deployment includes six main components:

1. **Admin Dashboard** (Port 9000) - System monitoring and management
2. **Marketplace UI** (Port 3000) - React-based user interface with advanced features
3. **Ledger API** (Port 8080) - REST API with authentication and package management
4. **WebSocket Server** (Port 8081) - Real-time communication system
5. **Documentation Site** (Port 8002) - MkDocs-based documentation
6. **Performance Monitoring** - Real-time metrics and monitoring dashboard

## Quick Start

### Automated Launch (Recommended)

Use the provided launch script to start all services:

```bash
# Windows
launch-web-interfaces.bat

# Linux/macOS
chmod +x launch-web-interfaces.sh
./launch-web-interfaces.sh
```

### Service Status Check

Monitor service health:

```bash
# Windows
check-services.bat

# Linux/macOS
./check-services.sh
```

## Individual Service Deployment

### 1. Ledger API with Authentication & WebSocket

The core API service provides REST endpoints, authentication, and WebSocket functionality:

```bash
cd runtime/ledger

# Install dependencies
npm install

# Environment variables (optional)
export JWT_SECRET="your-production-secret-key"
export WS_PORT="8081"
export PORT="8080"

# Start production server
npm run start
# Or for development with auto-reload
npm run dev:minimal
```

**Production Configuration:**

```javascript
// runtime/ledger/.env
JWT_SECRET=your-256-bit-secret-key-here
WS_PORT=8081
PORT=8080
NODE_ENV=production
REDIS_URL=redis://localhost:6379  # Optional for scaling
```

**Features:**
- JWT-based authentication with 24-hour tokens
- WebSocket server with room-based messaging
- Package management with real-time notifications
- Performance optimizations with caching and compression
- Security headers and rate limiting

### 2. Admin Dashboard

Enhanced monitoring dashboard with real-time capabilities:

```bash
cd admin-interface

# Start with enhanced features
node server.js
```

**Features:**
- Real-time service monitoring
- Performance metrics dashboard
- Security headers and compression
- Link to comprehensive monitoring interface

**Access:** http://localhost:9000

### 3. Marketplace UI

React-based interface with advanced search and authentication:

```bash
cd marketplace/ui

# Install dependencies (including build tools)
npm install

# Production build
npm run build

# Development server with hot reload
npm start

# Or production server
serve -s build -l 3000
```

**Features:**
- JWT-based authentication with login/registration
- Advanced search with fuzzy matching and filtering
- Real-time WebSocket integration
- Performance optimizations with code splitting
- Responsive design with Tailwind CSS

**Access:** http://localhost:3000

### 4. Documentation Site

Enhanced documentation with new feature guides:

```bash
# Install MkDocs and dependencies
pip install mkdocs mkdocs-material mkdocs-mermaid2-plugin

# Start documentation server
mkdocs serve --dev-addr=127.0.0.1:8002

# Production build
mkdocs build
```

**Access:** http://127.0.0.1:8002

## Production Optimizations

### Performance Enhancements

1. **Caching Strategy**
   - **API Level**: 5-minute in-memory cache for GET requests
   - **Frontend**: Service worker caching (recommended)
   - **CDN**: Static asset distribution (recommended)

2. **Compression**
   - **Gzip/Brotli**: Automatic compression for text-based content
   - **Asset Optimization**: Webpack bundle optimization
   - **Image Optimization**: Optimized image loading

3. **Code Splitting**
   - **React Components**: Lazy loading for non-critical components
   - **Webpack Chunks**: Vendor and common code separation
   - **Dynamic Imports**: Route-based code splitting

### Security Configuration

1. **JWT Security**
   ```javascript
   // Strong secret key (use environment variable)
   const JWT_SECRET = process.env.JWT_SECRET || 'change-this-in-production';
   
   // Token expiration
   const TOKEN_EXPIRY = '24h';
   
   // Secure token storage (consider httpOnly cookies)
   ```

2. **Security Headers**
   ```javascript
   // Applied automatically to all responses
   'X-Content-Type-Options': 'nosniff'
   'X-Frame-Options': 'DENY'
   'X-XSS-Protection': '1; mode=block'
   'Referrer-Policy': 'strict-origin-when-cross-origin'
   'Content-Security-Policy': "default-src 'self'; ..."
   ```

3. **HTTPS Configuration** (Recommended)
   ```nginx
   # Nginx configuration for HTTPS
   server {
       listen 443 ssl;
       server_name your-domain.com;
       
       ssl_certificate /path/to/certificate.crt;
       ssl_certificate_key /path/to/private.key;
       
       # Admin Dashboard
       location / {
           proxy_pass http://localhost:9000;
           proxy_set_header Host $host;
           proxy_set_header X-Real-IP $remote_addr;
       }
       
       # API Endpoints
       location /api/ {
           proxy_pass http://localhost:8080/;
           proxy_set_header Host $host;
           proxy_set_header X-Real-IP $remote_addr;
       }
       
       # WebSocket Proxy
       location /ws/ {
           proxy_pass http://localhost:8081/;
           proxy_http_version 1.1;
           proxy_set_header Upgrade $http_upgrade;
           proxy_set_header Connection "upgrade";
       }
       
       # Marketplace UI
       location /marketplace/ {
           proxy_pass http://localhost:3000/;
           proxy_set_header Host $host;
           proxy_set_header X-Real-IP $remote_addr;
       }
   }
   ```

## Container Deployment

### Docker Compose

```yaml
# docker-compose.yml
version: '3.8'
services:
  ledger-api:
    build:
      context: ./runtime/ledger
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
      - "8081:8081"
    environment:
      - JWT_SECRET=${JWT_SECRET}
      - NODE_ENV=production
    volumes:
      - ./runtime/ledger:/app
    restart: unless-stopped

  admin-dashboard:
    build:
      context: ./admin-interface
      dockerfile: Dockerfile
    ports:
      - "9000:9000"
    restart: unless-stopped

  marketplace-ui:
    build:
      context: ./marketplace/ui
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
    environment:
      - REACT_APP_API_URL=http://ledger-api:8080
      - REACT_APP_WS_URL=ws://ledger-api:8081
    depends_on:
      - ledger-api
    restart: unless-stopped

  documentation:
    build:
      context: .
      dockerfile: docs/Dockerfile
    ports:
      - "8002:8002"
    restart: unless-stopped

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    restart: unless-stopped
```

### Kubernetes Deployment

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: provability-fabric-web
spec:
  replicas: 3
  selector:
    matchLabels:
      app: provability-fabric-web
  template:
    metadata:
      labels:
        app: provability-fabric-web
    spec:
      containers:
      - name: ledger-api
        image: provability-fabric/ledger-api:latest
        ports:
        - containerPort: 8080
        - containerPort: 8081
        env:
        - name: JWT_SECRET
          valueFrom:
            secretKeyRef:
              name: jwt-secret
              key: secret
        - name: NODE_ENV
          value: "production"
        
      - name: admin-dashboard
        image: provability-fabric/admin-dashboard:latest
        ports:
        - containerPort: 9000
        
      - name: marketplace-ui
        image: provability-fabric/marketplace-ui:latest
        ports:
        - containerPort: 3000
        env:
        - name: REACT_APP_API_URL
          value: "http://ledger-api:8080"

---
apiVersion: v1
kind: Service
metadata:
  name: provability-fabric-service
spec:
  selector:
    app: provability-fabric-web
  ports:
  - name: admin
    port: 9000
    targetPort: 9000
  - name: api
    port: 8080
    targetPort: 8080
  - name: websocket
    port: 8081
    targetPort: 8081
  - name: ui
    port: 3000
    targetPort: 3000
  type: LoadBalancer
```

## Environment Configuration

### Environment Variables

Create a `.env` file for production configuration:

```bash
# .env
# JWT Configuration
JWT_SECRET=your-super-secure-256-bit-secret-key-here

# API Configuration
PORT=8080
WS_PORT=8081
NODE_ENV=production

# Database Configuration (optional)
REDIS_URL=redis://localhost:6379
POSTGRES_URL=postgresql://user:password@localhost:5432/provability_fabric

# Frontend Configuration
REACT_APP_API_URL=http://localhost:8080
REACT_APP_WS_URL=ws://localhost:8081

# Security Configuration
CORS_ORIGIN=https://your-domain.com
RATE_LIMIT_WINDOW=15
RATE_LIMIT_MAX=100

# Performance Configuration
CACHE_TTL=300000
COMPRESSION_LEVEL=6
```

### Production Secrets Management

For production deployments, use proper secret management:

```bash
# Kubernetes Secrets
kubectl create secret generic jwt-secret --from-literal=secret="your-jwt-secret"

# Docker Secrets
echo "your-jwt-secret" | docker secret create jwt_secret -

# Environment-specific files
.env.production
.env.staging
.env.development
```

## Monitoring and Observability

### Health Checks

All services provide health check endpoints:

```bash
# API Health
curl http://localhost:8080/health

# WebSocket Health
wscat -c ws://localhost:8081?token=<jwt-token>

# Admin Dashboard
curl http://localhost:9000

# Marketplace UI
curl http://localhost:3000

# Documentation
curl http://localhost:8002
```

### Logging Configuration

```javascript
// Enhanced logging for production
const winston = require('winston');

const logger = winston.createLogger({
  level: process.env.LOG_LEVEL || 'info',
  format: winston.format.combine(
    winston.format.timestamp(),
    winston.format.errors({ stack: true }),
    winston.format.json()
  ),
  transports: [
    new winston.transports.File({ filename: 'error.log', level: 'error' }),
    new winston.transports.File({ filename: 'combined.log' }),
    new winston.transports.Console({
      format: winston.format.simple()
    })
  ]
});
```

### Metrics Collection

```javascript
// Basic metrics collection
const metrics = {
  connections: 0,
  requests: 0,
  errors: 0,
  responseTime: [],
  
  recordRequest: (duration) => {
    metrics.requests++;
    metrics.responseTime.push(duration);
  },
  
  getAverageResponseTime: () => {
    const sum = metrics.responseTime.reduce((a, b) => a + b, 0);
    return sum / metrics.responseTime.length || 0;
  }
};
```

## Performance Monitoring

### Real-Time Dashboard

Access the enhanced monitoring dashboard:
- **URL**: http://localhost:9000/monitoring.html
- **Features**: 
  - Live service status updates
  - Performance metrics with charts
  - System resource monitoring
  - Real-time log streaming
  - Connection and request analytics

### Performance Metrics

Key metrics to monitor:

| Metric | Target | Alert Threshold |
|--------|--------|-----------------|
| API Response Time | < 200ms | > 500ms |
| WebSocket Connections | Stable | > 1000 concurrent |
| Memory Usage | < 512MB | > 1GB |
| CPU Usage | < 50% | > 80% |
| Error Rate | < 1% | > 5% |

## Scaling Considerations

### Horizontal Scaling

For high-traffic deployments:

1. **Load Balancer Configuration**
   ```nginx
   upstream api_backend {
       server localhost:8080;
       server localhost:8081;
       server localhost:8082;
   }
   
   upstream websocket_backend {
       ip_hash;  # Sticky sessions for WebSocket
       server localhost:8081;
       server localhost:8082;
       server localhost:8083;
   }
   ```

2. **Database Scaling**
   - Redis cluster for session storage
   - PostgreSQL read replicas for data
   - Connection pooling

3. **WebSocket Scaling**
   - Redis pub/sub for message broadcasting
   - Sticky sessions for connection persistence
   - Connection load balancing

### Vertical Scaling

Resource recommendations:

| Component | CPU | Memory | Storage |
|-----------|-----|--------|---------|
| Ledger API | 2 cores | 2GB | 10GB |
| Admin Dashboard | 1 core | 512MB | 5GB |
| Marketplace UI | 1 core | 1GB | 5GB |
| Documentation | 0.5 core | 256MB | 2GB |
| Redis (optional) | 1 core | 1GB | 5GB |

## Troubleshooting

### Common Issues

1. **WebSocket Connection Failed**
   ```bash
   # Check WebSocket server
   netstat -an | grep 8081
   
   # Test WebSocket connection
   wscat -c ws://localhost:8081?token=<jwt-token>
   ```

2. **Authentication Not Working**
   ```bash
   # Check JWT secret configuration
   echo $JWT_SECRET
   
   # Test API authentication
   curl -H "Authorization: Bearer <token>" http://localhost:8080/auth/profile
   ```

3. **Search Not Working**
   ```bash
   # Check package data loading
   curl http://localhost:8080/packages
   
   # Check search endpoint
   curl "http://localhost:8080/search?q=test"
   ```

4. **Performance Issues**
   ```bash
   # Check service status
   ./check-services.sh
   
   # Monitor resource usage
   top -p $(pgrep -f "node")
   ```

### Debug Mode

Enable debug logging:

```bash
# Set debug environment variables
export DEBUG=provability-fabric:*
export LOG_LEVEL=debug

# Start services with verbose logging
npm run dev:minimal
```

### Service Recovery

Automatic service restart configuration:

```bash
# systemd service example
[Unit]
Description=Provability-Fabric Ledger API
After=network.target

[Service]
Type=simple
User=www-data
WorkingDirectory=/path/to/provability-fabric/runtime/ledger
ExecStart=/usr/bin/node minimal-server.js
Restart=always
RestartSec=10
Environment=NODE_ENV=production
Environment=JWT_SECRET=your-secret-here

[Install]
WantedBy=multi-user.target
```

## Backup and Recovery

### Data Backup

```bash
# Backup configuration files
tar -czf config-backup.tar.gz .env runtime/ledger/package.json marketplace/ui/package.json

# Backup user data (if using persistent storage)
pg_dump provability_fabric > backup.sql

# Backup Redis data (if using Redis)
redis-cli BGSAVE
```

### Disaster Recovery

```bash
# Service recovery script
#!/bin/bash
services=("admin-interface" "marketplace/ui" "runtime/ledger")

for service in "${services[@]}"; do
    echo "Starting $service..."
    cd "$service"
    npm start &
    cd ..
done

echo "All services started"
```