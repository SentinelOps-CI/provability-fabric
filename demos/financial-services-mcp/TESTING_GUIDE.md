# Financial Services MCP - Comprehensive Testing Guide

This document provides detailed instructions for testing and debugging the Financial Services MCP demonstration system.

## 🎯 Overview

The testing suite provides comprehensive validation of all 8 major components:

1. **High-Performance MCP Server** - Sub-millisecond transaction processing
2. **AI Fraud Detection Agent** - Real-time pattern recognition
3. **Audit Trail Service** - Blockchain-inspired immutable logging
4. **Performance Benchmarking** - Multi-worker throughput testing
5. **Multi-Tenant Database** - PostgreSQL with row-level security
6. **Real-Time Dashboard** - React-based monitoring
7. **End-to-End Integration** - Complete system validation
8. **Production Infrastructure** - Docker Compose deployment

## 🚀 Quick Start

### Prerequisites

```bash
# Node.js 20+ and npm 10+
node --version  # Should be 20.0.0 or higher
npm --version   # Should be 10.0.0 or higher

# PostgreSQL 15+
psql --version  # Should be 15.0 or higher

# Redis 7+
redis-server --version  # Should be 7.0 or higher

# Docker and Docker Compose
docker --version
docker-compose --version
```

### Environment Setup

```bash
# 1. Install dependencies
cd demos/financial-services-mcp
npm install

# 2. Start infrastructure services
docker-compose up -d postgres-fintech redis-cache

# 3. Initialize database
npm run setup-database

# 4. Start application services
npm run docker:up

# 5. Wait for services to be ready (about 30 seconds)
npm run docker:logs
```

### Running Tests

```bash
# Run all critical tests (recommended for CI/CD)
npm run test:all:critical

# Run complete test suite
npm run test:all

# Run specific test categories
npm run test:enhanced      # Performance and accuracy tests
npm run test:security      # Security and audit validation
npm run test:stress        # Extreme load testing
npm run test:integration   # Basic integration tests

# Run tests in parallel (faster execution)
npm run test:all:parallel

# Generate coverage report
npm run test:coverage
```

## 📊 Test Suites

### 1. Enhanced Integration Test Suite

**File:** `tests/enhanced-test-suite.ts`  
**Duration:** ~8 minutes  
**Priority:** Critical

Tests ultra-low latency performance, high-throughput scenarios, and fraud detection accuracy.

**Key Metrics:**
- Ultra-low latency: < 0.5ms for critical operations
- High throughput: 5000+ TPS sustained load
- Fraud detection accuracy: 99.5%+ with labeled data
- Multi-tenant isolation: Complete data separation

```bash
# Run enhanced tests
npm run test:enhanced

# Sample output
🧪 Enhanced Integration Tests
   ✅ Ultra-low latency fraud detection (< 0.5ms)
   ✅ High-throughput sustained load (5000+ TPS)
   ✅ Concurrent multi-tenant performance isolation
   ✅ High-accuracy fraud detection with labeled data
```

### 2. Security and Audit Test Suite

**File:** `tests/security-audit-test-suite.ts`  
**Duration:** ~6 minutes  
**Priority:** Critical

Validates security controls and audit trail integrity.

**Security Tests:**
- SQL injection resistance
- Cross-site scripting (XSS) protection
- Database access control validation
- Multi-tenant data isolation

**Audit Tests:**
- Chain integrity verification
- Immutability enforcement
- Event completeness validation
- Performance under load

```bash
# Run security tests
npm run test:security

# Sample output
🔒 Security and Audit Tests
   ✅ SQL injection resistance (100% blocked)
   ✅ Cross-site scripting (XSS) protection
   ✅ Database access control validation
   ✅ Multi-tenant data isolation
   ✅ Audit chain integrity verification
   ✅ Audit trail immutability enforcement
```

### 3. Stress Test Suite

**File:** `tests/stress-test-suite.ts`  
**Duration:** ~12 minutes  
**Priority:** Medium

Tests system behavior under extreme load conditions.

**Stress Scenarios:**
- Breaking point analysis (1000+ concurrent users)
- Memory leak detection
- Connection pool exhaustion
- Resource limit validation

```bash
# Run stress tests (warning: resource intensive)
npm run test:stress

# Sample output
💥 Stress Tests
   ✅ Breaking point analysis (1000 users, 10 TPS each)
   ✅ Memory leak detection (sustained load)
   ✅ Connection pool exhaustion resilience
```

### 4. Original Integration Test Suite

**File:** `tests/integration-test-suite.ts`  
**Duration:** ~4 minutes  
**Priority:** High

Baseline integration tests covering core functionality.

```bash
# Run original integration tests
npm run test:integration
```

## 🎯 Performance Thresholds

### Latency Requirements

| Operation Type | Target | Maximum |
|---------------|--------|---------|
| Ultra-critical | < 0.5ms | 1ms |
| Low-latency | < 1ms | 2ms |
| Normal operations | < 5ms | 10ms |
| Complex operations | < 10ms | 20ms |

### Throughput Requirements

| Scenario | Minimum | Target |
|----------|---------|--------|
| Fraud detection | 2,000 TPS | 5,000 TPS |
| Audit logging | 10,000 TPS | 20,000 TPS |
| MCP operations | 1,000 TPS | 3,000 TPS |
| End-to-end pipeline | 500 TPS | 1,000 TPS |

### Accuracy Requirements

| Metric | Minimum | Target |
|--------|---------|--------|
| Fraud detection accuracy | 99.5% | 99.8% |
| Data integrity | 100% | 100% |
| Audit completeness | 100% | 100% |
| System availability | 99.95% | 99.99% |

## 🔧 Test Configuration

### Environment Variables

```bash
# Service URLs (defaults for local development)
export MCP_SERVER_URL="http://localhost:8080"
export FRAUD_AGENT_URL="http://localhost:8082"
export AUDIT_SERVICE_URL="http://localhost:8083"
export DASHBOARD_URL="http://localhost:3001"

# Database connections
export DATABASE_URL="postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services"
export REDIS_URL="redis://localhost:6380"

# Test parameters
export TEST_DURATION_MS="300000"      # 5 minutes
export CONCURRENT_USERS="50"
export TARGET_THROUGHPUT="1000"       # TPS
export TARGET_LATENCY_MS="1.0"
export ENABLE_STRESS_TEST="false"     # Set to "true" for stress testing
```

### Jest Configuration

The test suite uses Jest with custom matchers for financial services testing:

```typescript
// Custom matchers available in all tests
expect(latency).toBeWithinLatencyThreshold(1.0); // < 1ms
expect(throughput).toMeetThroughputRequirement(1000); // >= 1000 TPS
expect(fraudAnalysis).toHaveValidFraudProbability();
expect(auditEvent).toBeValidAuditEvent();
expect(response).toHaveSecureHash();
expect(report).toMeetComplianceRequirements();
```

## 📈 Performance Monitoring

### Real-Time Metrics

During test execution, monitor key metrics:

```bash
# View service logs
npm run docker:logs

# Monitor system resources
top -p $(pgrep -f "financial-mcp")

# Check database performance
psql -d financial_services -c "
  SELECT 
    schemaname,
    tablename,
    seq_scan,
    seq_tup_read,
    idx_scan,
    idx_tup_fetch
  FROM pg_stat_user_tables 
  ORDER BY seq_tup_read DESC;
"
```

### Performance Dashboards

Access real-time monitoring dashboards:

- **Grafana Dashboard**: http://localhost:3000
  - Username: admin
  - Password: admin
- **Prometheus Metrics**: http://localhost:9090
- **Application Dashboard**: http://localhost:3001

## 🐛 Debugging Guide

### Common Issues

#### 1. Service Startup Failures

```bash
# Check service health
curl http://localhost:8080/health
curl http://localhost:8082/health
curl http://localhost:8083/health

# Check logs for errors
docker-compose logs financial-mcp-server
docker-compose logs fraud-detection-agent
docker-compose logs audit-verifier
```

#### 2. Database Connection Issues

```bash
# Test database connectivity
psql -d financial_services -c "SELECT 1;"

# Check connection pool status
psql -d financial_services -c "
  SELECT 
    state,
    count(*) 
  FROM pg_stat_activity 
  WHERE datname = 'financial_services' 
  GROUP BY state;
"
```

#### 3. Performance Issues

```bash
# Check Redis performance
redis-cli --latency -h localhost -p 6380

# Monitor query performance
psql -d financial_services -c "
  SELECT 
    query,
    calls,
    total_time,
    mean_time,
    max_time
  FROM pg_stat_statements 
  ORDER BY total_time DESC 
  LIMIT 10;
"
```

#### 4. Test Failures

```bash
# Run tests with verbose output
npm run test:enhanced -- --verbose

# Run specific test file
npx jest tests/enhanced-test-suite.ts --verbose

# Debug test with node inspector
node --inspect-brk ./node_modules/.bin/jest tests/enhanced-test-suite.ts
```

### Log Analysis

```bash
# Check application logs
tail -f financial-mcp-server.log
tail -f fraud-detection-agent.log
tail -f audit-trail-service.log

# Filter for errors
grep -i error *.log

# Monitor performance metrics
grep -i "latency\|throughput\|performance" *.log
```

## 📋 Test Reports

### Automated Report Generation

```bash
# Generate comprehensive test report
npm run test:all

# Reports are saved to ./reports/ directory:
# - comprehensive-test-report-YYYY-MM-DD.json
# - comprehensive-test-report-YYYY-MM-DD.md
```

### Report Contents

1. **Executive Summary**
   - Overall pass/fail status
   - Test suite completion rates
   - Critical issues identified

2. **Performance Metrics**
   - Latency percentiles (P50, P95, P99)
   - Throughput measurements
   - Resource utilization

3. **Security Analysis**
   - Vulnerability test results
   - Audit trail integrity
   - Compliance validation

4. **Recommendations**
   - Performance optimizations
   - Security improvements
   - Infrastructure scaling

## 🔄 Continuous Integration

### GitHub Actions Integration

Add to `.github/workflows/test.yml`:

```yaml
name: Comprehensive Testing

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    
    services:
      postgres:
        image: postgres:15
        env:
          POSTGRES_PASSWORD: secure_fintech_2025
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
      
      redis:
        image: redis:7
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'
      
      - name: Install dependencies
        run: npm ci
      
      - name: Setup database
        run: npm run setup-database
      
      - name: Run critical tests
        run: npm run test:all:critical
      
      - name: Upload test reports
        uses: actions/upload-artifact@v4
        with:
          name: test-reports
          path: reports/
```

### Docker-based CI

```bash
# Run tests in Docker environment
docker-compose -f docker-compose.test.yml up --abort-on-container-exit
```

## 📚 Additional Resources

### Documentation

- [MCP Protocol Specification](https://modelcontextprotocol.io/docs)
- [Financial Services Architecture](./README.md)
- [Security Implementation](./docs/security.md)
- [Performance Optimization](./docs/performance.md)

### External Tools

- [Artillery.js](https://artillery.io/) - Load testing
- [k6](https://k6.io/) - Performance testing
- [Postman](https://postman.com/) - API testing
- [DataDog](https://datadog.com/) - Production monitoring

### Support

For issues and questions:

1. Check the [troubleshooting guide](./docs/troubleshooting.md)
2. Review test logs and error messages
3. Consult the [FAQ](./docs/faq.md)
4. Open an issue on the project repository

---

**Note:** This testing suite is designed for comprehensive validation of a production-ready financial services system. Always run tests in a dedicated testing environment, never against production data.
