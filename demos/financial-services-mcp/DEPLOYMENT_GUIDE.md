# Financial Services MCP Demo - Deployment Guide

This guide provides step-by-step instructions for deploying the Financial Services Model Context Protocol (MCP) demonstration environment.

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Quick Start](#quick-start)
3. [Component Architecture](#component-architecture)
4. [Detailed Setup](#detailed-setup)
5. [Configuration](#configuration)
6. [Performance Testing](#performance-testing)
7. [Monitoring](#monitoring)
8. [Troubleshooting](#troubleshooting)
9. [Security Considerations](#security-considerations)

## Prerequisites

### System Requirements

- **Operating System**: Linux (Ubuntu 20.04+ recommended), macOS, or Windows with WSL2
- **CPU**: Minimum 8 cores, recommended 16+ cores for optimal performance
- **Memory**: Minimum 16GB RAM, recommended 32GB+ for full load testing
- **Storage**: Minimum 50GB free space (SSD recommended)
- **Network**: High-speed internet connection for container downloads

### Software Dependencies

- **Docker**: Version 20.10+
- **Docker Compose**: Version 2.0+
- **Node.js**: Version 18.0+ (for development and testing)
- **Git**: Latest version
- **curl**: For API testing

### Development Tools (Optional)

- **PostgreSQL Client**: For database inspection
- **Redis CLI**: For cache inspection
- **k6** or **Artillery**: For additional load testing

## Quick Start

### 1. Clone and Setup

```bash
# Clone the repository
git clone <repository-url>
cd demos/financial-services-mcp

# Make scripts executable
chmod +x scripts/*.sh

# Run the quick setup script
./scripts/quick-setup.sh
```

### 2. Start the Demo Environment

```bash
# Start all services
docker-compose up -d

# Check service status
docker-compose ps

# View logs (optional)
docker-compose logs -f
```

### 3. Verify Deployment

```bash
# Run health checks
./scripts/health-check.sh

# Run basic integration tests
npm test

# Access the monitoring dashboard
open http://localhost:3001/dashboard
```

## Component Architecture

The demonstration consists of the following components:

### Core Services

1. **Financial MCP Server** (Port 8080)
   - High-performance MCP server optimized for financial transactions
   - Implements MCP tools for fraud detection and transaction analysis
   - Multi-tenant support with row-level security

2. **Fraud Detection Agent** (Port 8082)
   - AI-powered fraud detection with sub-millisecond response times
   - Pattern recognition and real-time risk assessment
   - Machine learning model for fraud probability calculation

3. **Audit Trail Service** (Port 8083)
   - Blockchain-inspired immutable audit logging
   - Cryptographic verification of audit chain integrity
   - Compliance reporting for financial regulations

4. **Monitoring Dashboard** (Port 3001)
   - Real-time performance and compliance monitoring
   - Multi-tenant metrics visualization
   - Regulatory compliance reporting interface

### Supporting Infrastructure

5. **PostgreSQL Database** (Port 5433)
   - Optimized for high-performance financial data
   - Row-level security for multi-tenant isolation
   - Comprehensive indexing for sub-millisecond queries

6. **Redis Cache** (Port 6380)
   - Ultra-low latency caching for fraud patterns
   - Real-time metrics storage
   - Session and pattern cache management

7. **Performance Monitoring Stack**
   - **Prometheus** (Port 9090): Metrics collection
   - **Grafana** (Port 3000): Advanced analytics visualization
   - **NGINX Load Balancer** (Port 80/443): Production-ready routing

## Detailed Setup

### Step 1: Environment Preparation

```bash
# Create necessary directories
mkdir -p logs reports data

# Set environment variables
export COMPOSE_PROJECT_NAME=financial-mcp
export NODE_ENV=production
export LOG_LEVEL=info

# Configure Docker resources (recommended)
# Ensure Docker has at least 8GB RAM and 4 CPU cores allocated
```

### Step 2: Database Initialization

```bash
# Start database first
docker-compose up -d postgres-fintech

# Wait for database to be ready
./scripts/wait-for-db.sh

# Initialize schema and test data
docker-compose exec postgres-fintech psql -U fintech_user -d financial_services -f /docker-entrypoint-initdb.d/init.sql
```

### Step 3: Service Deployment

```bash
# Start infrastructure services
docker-compose up -d redis-cache postgres-fintech

# Start core application services
docker-compose up -d financial-mcp-server fraud-detection-agent audit-verifier

# Start monitoring and dashboard
docker-compose up -d monitoring-dashboard prometheus grafana

# Start load balancer
docker-compose up -d nginx-lb
```

### Step 4: Verification

```bash
# Check all services are healthy
curl http://localhost:8080/health  # MCP Server
curl http://localhost:8082/health  # Fraud Agent
curl http://localhost:8083/health  # Audit Service
curl http://localhost:3001/health  # Dashboard

# Run integration tests
npm run test:integration

# Run performance benchmarks
npm run benchmark
```

## Configuration

### Environment Variables

Create a `.env` file with the following variables:

```bash
# Database Configuration
DATABASE_URL=postgresql://fintech_user:secure_fintech_2025@postgres-fintech:5432/financial_services
REDIS_URL=redis://redis-cache:6379

# Service Configuration
MCP_SERVER_PORT=8080
FRAUD_AGENT_PORT=8082
AUDIT_SERVICE_PORT=8083
DASHBOARD_PORT=3001

# Performance Tuning
MAX_CONCURRENT_TRANSACTIONS=10000
CACHE_SIZE=100000
WORKER_THREADS=8

# Security Configuration
JWT_SECRET=your-jwt-secret-here
ENCRYPTION_KEY=your-encryption-key-here
AUTH0_DOMAIN=your-auth0-domain
AUTH0_AUDIENCE=your-auth0-audience

# Monitoring Configuration
PROMETHEUS_RETENTION=30d
GRAFANA_ADMIN_PASSWORD=admin
LOG_RETENTION_DAYS=90

# Performance Thresholds
TARGET_LATENCY_MS=1.0
TARGET_THROUGHPUT_TPS=5000
FRAUD_DETECTION_THRESHOLD=0.85
```

### Advanced Configuration

#### Database Performance Tuning

Edit `docker-compose.yml` for PostgreSQL optimization:

```yaml
postgres-fintech:
  command: >
    postgres
    -c shared_preload_libraries=pg_stat_statements
    -c max_connections=1000
    -c shared_buffers=512MB
    -c effective_cache_size=2GB
    -c work_mem=16MB
    -c maintenance_work_mem=128MB
    -c random_page_cost=1.1
    -c checkpoint_completion_target=0.9
```

#### Redis Configuration

Create `redis.conf` for optimal performance:

```
maxmemory 1gb
maxmemory-policy allkeys-lru
save ""
appendonly no
tcp-nodelay yes
tcp-keepalive 60
```

#### NGINX Load Balancer

Configure `nginx/nginx.conf` for production:

```nginx
upstream mcp_backend {
    least_conn;
    server financial-mcp-server:8080 max_fails=3 fail_timeout=30s;
}

upstream fraud_backend {
    least_conn;
    server fraud-detection-agent:8082 max_fails=3 fail_timeout=30s;
}

server {
    listen 80;
    client_max_body_size 10M;
    client_body_timeout 30s;
    client_header_timeout 30s;
    
    location /api/mcp/ {
        proxy_pass http://mcp_backend/;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_timeout 5s;
    }
    
    location /api/fraud/ {
        proxy_pass http://fraud_backend/;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_timeout 2s;
    }
}
```

## Performance Testing

### Benchmark Suite

Run the comprehensive performance benchmark:

```bash
# Full benchmark suite (30 minutes)
npm run benchmark:full

# Quick performance check (5 minutes)
npm run benchmark:quick

# Stress test (high load, 15 minutes)
npm run benchmark:stress

# Latency-focused test
npm run benchmark:latency
```

### Load Testing with k6

Install k6 and run targeted load tests:

```bash
# Install k6
sudo apt install k6  # Ubuntu
brew install k6      # macOS

# Run fraud detection load test
k6 run tests/load/fraud-detection.js

# Run MCP server load test
k6 run tests/load/mcp-server.js

# Run end-to-end workflow test
k6 run tests/load/e2e-workflow.js
```

### Performance Expectations

#### Target Performance Metrics

| Component | Metric | Target | Threshold |
|-----------|---------|---------|-----------|
| Fraud Detection | P95 Latency | < 1ms | < 2ms |
| MCP Server | P95 Latency | < 2ms | < 5ms |
| Audit Service | P95 Latency | < 0.5ms | < 1ms |
| End-to-End | P95 Latency | < 5ms | < 10ms |
| System | Throughput | > 5000 TPS | > 2000 TPS |
| System | Availability | > 99.9% | > 99.5% |

#### Hardware Scaling Guidelines

| Concurrent Users | CPU Cores | RAM | Expected TPS |
|------------------|-----------|-----|--------------|
| 100 | 4 cores | 8GB | 1,000 |
| 500 | 8 cores | 16GB | 3,000 |
| 1,000 | 16 cores | 32GB | 5,000 |
| 5,000 | 32 cores | 64GB | 15,000 |

## Monitoring

### Access Monitoring Interfaces

1. **Application Dashboard**: http://localhost:3001
   - Real-time transaction monitoring
   - Fraud detection metrics
   - Compliance reporting

2. **Prometheus**: http://localhost:9090
   - Raw metrics and alerting
   - Custom queries and analysis

3. **Grafana**: http://localhost:3000
   - Advanced visualization dashboards
   - Historical trend analysis
   - Alert management

### Key Metrics to Monitor

#### Performance Metrics
- Transaction processing latency (P50, P95, P99)
- Throughput (transactions per second)
- Error rates and availability
- Resource utilization (CPU, memory, network)

#### Business Metrics
- Fraud detection accuracy
- False positive rates
- Transaction approval rates
- Regulatory compliance scores

#### Infrastructure Metrics
- Database connection pool utilization
- Cache hit rates
- Network latency between services
- Disk I/O and storage usage

### Alerting Configuration

Create alerts for critical thresholds:

```yaml
# prometheus/alerts.yml
groups:
  - name: financial-mcp-alerts
    rules:
      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.005
        for: 2m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "P95 latency is above 5ms"

      - alert: LowThroughput
        expr: rate(transactions_total[5m]) < 1000
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Low throughput detected"
          description: "Transaction rate is below 1000 TPS"

      - alert: FraudDetectionDown
        expr: up{job="fraud-detection-agent"} == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "Fraud detection service is down"
```

## Troubleshooting

### Common Issues

#### 1. Services Not Starting

**Symptoms**: Services fail to start or exit immediately

**Solutions**:
```bash
# Check Docker resources
docker system df
docker system prune -f

# Check logs
docker-compose logs [service-name]

# Restart individual services
docker-compose restart [service-name]

# Full restart
docker-compose down && docker-compose up -d
```

#### 2. Database Connection Issues

**Symptoms**: Services can't connect to PostgreSQL

**Solutions**:
```bash
# Check database status
docker-compose exec postgres-fintech pg_isready

# Check connection from service
docker-compose exec financial-mcp-server nc -z postgres-fintech 5432

# Reset database
docker-compose down postgres-fintech
docker volume rm financial-mcp_postgres_fintech_data
docker-compose up -d postgres-fintech
```

#### 3. High Latency Issues

**Symptoms**: Response times exceed targets

**Solutions**:
```bash
# Check resource usage
docker stats

# Optimize database
docker-compose exec postgres-fintech psql -U fintech_user -d financial_services -c "VACUUM ANALYZE;"

# Clear Redis cache
docker-compose exec redis-cache redis-cli FLUSHALL

# Scale services
docker-compose up -d --scale financial-mcp-server=3
```

#### 4. Memory Issues

**Symptoms**: Out of memory errors, container restarts

**Solutions**:
```bash
# Increase Docker memory limits
# Edit docker-compose.yml:
services:
  financial-mcp-server:
    deploy:
      resources:
        limits:
          memory: 2GB
        reservations:
          memory: 1GB

# Monitor memory usage
docker stats --no-stream

# Enable memory profiling
export NODE_OPTIONS="--max-old-space-size=4096"
```

### Performance Debugging

#### Enable Debug Logging

```bash
# Set debug environment variables
export LOG_LEVEL=debug
export DEBUG=*

# Restart services with debug logging
docker-compose down && docker-compose up -d
```

#### Profile Performance

```bash
# Enable Node.js profiling
export NODE_OPTIONS="--prof --prof-process-all"

# Generate heap snapshots
kill -SIGUSR2 $(docker-compose exec financial-mcp-server pidof node)

# Analyze with clinic.js
npm install -g clinic
clinic doctor -- node src/financial-mcp-server.js
```

### Log Analysis

```bash
# View real-time logs
docker-compose logs -f --tail=100

# Search for errors
docker-compose logs | grep -i error

# Export logs for analysis
docker-compose logs > logs/system-$(date +%Y%m%d-%H%M%S).log

# Monitor specific service
docker-compose logs -f fraud-detection-agent
```

## Security Considerations

### Production Security Checklist

#### 1. Authentication and Authorization

- [ ] Change all default passwords
- [ ] Configure Auth0 or similar OAuth provider
- [ ] Enable JWT token validation
- [ ] Implement API rate limiting
- [ ] Set up RBAC for multi-tenant access

#### 2. Network Security

- [ ] Enable HTTPS with valid certificates
- [ ] Configure firewall rules
- [ ] Use Docker networks for service isolation
- [ ] Enable audit logging for all API calls
- [ ] Implement IP whitelisting for admin access

#### 3. Data Protection

- [ ] Enable database encryption at rest
- [ ] Configure SSL/TLS for all database connections
- [ ] Implement field-level encryption for sensitive data
- [ ] Set up automated backup with encryption
- [ ] Configure Redis AUTH and SSL

#### 4. Monitoring and Alerting

- [ ] Set up security monitoring dashboards
- [ ] Configure alerts for suspicious activities
- [ ] Enable intrusion detection
- [ ] Implement log aggregation and analysis
- [ ] Set up compliance reporting

### Security Configuration

#### Enable HTTPS

```bash
# Generate SSL certificates (for development)
openssl req -x509 -nodes -days 365 -newkey rsa:2048 \
  -keyout nginx/ssl/server.key \
  -out nginx/ssl/server.crt

# Update nginx configuration for HTTPS
# Edit nginx/nginx.conf to include SSL configuration
```

#### Database Security

```sql
-- Create read-only monitoring user
CREATE USER monitoring_user WITH PASSWORD 'secure_monitor_password';
GRANT CONNECT ON DATABASE financial_services TO monitoring_user;
GRANT USAGE ON SCHEMA public TO monitoring_user;
GRANT SELECT ON ALL TABLES IN SCHEMA public TO monitoring_user;

-- Enable audit logging
ALTER SYSTEM SET log_statement = 'all';
ALTER SYSTEM SET log_line_prefix = '%t [%p]: [%l-1] user=%u,db=%d,app=%a,client=%h ';
SELECT pg_reload_conf();
```

#### Redis Security

```bash
# Configure Redis AUTH
echo "requirepass your_redis_password" >> redis.conf

# Update application configuration
export REDIS_URL=redis://:your_redis_password@redis-cache:6379
```

### Compliance Features

#### SOX Compliance

- Immutable audit trails with cryptographic verification
- Complete transaction logging with timestamps
- Role-based access controls with approval workflows
- Regular compliance reporting and verification

#### PCI DSS Requirements

- Encryption of payment card data in transit and at rest
- Secure key management and rotation
- Network segmentation and access controls
- Regular security testing and vulnerability assessments

#### Basel III Compliance

- Real-time risk calculation and monitoring
- Capital adequacy ratio tracking
- Stress testing and scenario analysis
- Regulatory reporting automation

## Conclusion

This deployment guide provides comprehensive instructions for setting up the Financial Services MCP demonstration environment. The system demonstrates how Model Context Protocol can be effectively used in financial services to achieve:

- **Sub-millisecond fraud detection** with high accuracy
- **Comprehensive audit trails** with cryptographic verification
- **Multi-tenant isolation** with enterprise-grade security
- **Real-time compliance monitoring** for financial regulations
- **Horizontal scalability** to handle enterprise-level transaction volumes

For additional support or questions, please refer to the project documentation or create an issue in the repository.

### Next Steps

1. **Production Deployment**: Follow the security checklist and configure production infrastructure
2. **Custom Integration**: Adapt the MCP tools for your specific financial services requirements
3. **Performance Optimization**: Use the benchmarking results to fine-tune for your workload
4. **Monitoring Setup**: Configure alerts and dashboards for your operational requirements
5. **Compliance Integration**: Connect to your existing compliance and risk management systems

The demonstration proves that MCP can deliver the performance, security, and compliance requirements necessary for production financial services applications.
