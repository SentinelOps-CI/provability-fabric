# Configuration Guide

This guide covers all configuration options for the Provability-Fabric framework, including environment-specific settings, security configurations, and deployment options.

## Overview

Provability-Fabric uses a hierarchical configuration system that supports:

- **Environment-specific configurations** - Development, staging, production
- **Component-specific settings** - API, verification engines, monitoring
- **Security configurations** - Authentication, encryption, access control
- **Deployment options** - Kubernetes, Docker, cloud platforms

## Configuration Structure

### Configuration Hierarchy

```
1. Default values (built-in)
2. Global config file (~/.config/provability-fabric/config.yaml)
3. Project config file (./provability-fabric.yaml)
4. Environment config file (./config/environments/{env}.yaml)
5. Command-line flags
6. Environment variables
```

### Configuration File Locations

```bash
# Global configuration
~/.config/provability-fabric/config.yaml

# Project configuration
./provability-fabric.yaml
./config/provability-fabric.yaml

# Environment-specific configuration
./config/environments/development.yaml
./config/environments/staging.yaml
./config/environments/production.yaml

# Component-specific configuration
./config/api.yaml
./config/verification.yaml
./config/monitoring.yaml
```

## Core Configuration

### Main Configuration File

```yaml
# provability-fabric.yaml
api:
  version: "v1"
  host: "0.0.0.0"
  port: 8080
  timeout: "30s"
  max_request_size: "10MB"
  cors:
    enabled: true
    allowed_origins: ["*"]
    allowed_methods: ["GET", "POST", "PUT", "DELETE"]
    allowed_headers: ["*"]

database:
  type: "postgresql"
  host: "localhost"
  port: 5432
  name: "provability_fabric"
  username: "${DB_USERNAME}"
  password: "${DB_PASSWORD}"
  ssl_mode: "require"
  max_connections: 100
  connection_timeout: "10s"
  idle_timeout: "300s"

redis:
  host: "localhost"
  port: 6379
  password: "${REDIS_PASSWORD}"
  database: 0
  pool_size: 10
  connection_timeout: "5s"

verification:
  lean:
    timeout: "300s"
    max_memory: "2GB"
    worker_pool_size: 4
  marabou:
    timeout: "600s"
    max_memory: "4GB"
    worker_pool_size: 2
  dryvr:
    timeout: "900s"
    max_memory: "8GB"
    worker_pool_size: 1

monitoring:
  enabled: true
  metrics_port: 9090
  health_check_port: 8081
  prometheus:
    enabled: true
    scrape_interval: "15s"
  grafana:
    enabled: true
    port: 3000

security:
  jwt:
    secret: "${JWT_SECRET}"
    expiration: "24h"
    refresh_expiration: "168h"
  encryption:
    key: "${ENCRYPTION_KEY}"
    algorithm: "AES-256-GCM"
  rate_limiting:
    enabled: true
    requests_per_minute: 100
    burst_size: 20

logging:
  level: "info"
  format: "json"
  output: "stdout"
  file:
    enabled: false
    path: "/var/log/provability-fabric"
    max_size: "100MB"
    max_age: "30d"
    max_backups: 10

kubernetes:
  context: "default"
  namespace: "provability-fabric"
  service_account: "default"
  image_pull_secrets: []
  resources:
    requests:
      cpu: "100m"
      memory: "128Mi"
    limits:
      cpu: "500m"
      memory: "512Mi"
```

## Environment-Specific Configuration

### Development Environment

```yaml
# config/environments/development.yaml
environment: development
debug: true

api:
  host: "localhost"
  port: 8080
  cors:
    allowed_origins: ["http://localhost:3000", "http://localhost:8080"]

database:
  host: "localhost"
  port: 5432
  name: "provability_fabric_dev"
  ssl_mode: "disable"

redis:
  host: "localhost"
  port: 6379
  password: ""

verification:
  lean:
    timeout: "60s"
    max_memory: "1GB"
    worker_pool_size: 2
  marabou:
    timeout: "120s"
    max_memory: "2GB"
    worker_pool_size: 1

monitoring:
  enabled: false
  metrics_port: 9090

logging:
  level: "debug"
  format: "text"
  output: "stdout"

kubernetes:
  context: "kind-provability-fabric"
  namespace: "provability-fabric-dev"
```

### Staging Environment

```yaml
# config/environments/staging.yaml
environment: staging
debug: false

api:
  host: "0.0.0.0"
  port: 8080
  cors:
    allowed_origins: ["https://staging.provability-fabric.org"]

database:
  host: "postgresql-staging.svc.cluster.local"
  port: 5432
  name: "provability_fabric_staging"
  ssl_mode: "require"

redis:
  host: "redis-staging.svc.cluster.local"
  port: 6379
  password: "${REDIS_PASSWORD}"

verification:
  lean:
    timeout: "180s"
    max_memory: "2GB"
    worker_pool_size: 3
  marabou:
    timeout: "300s"
    max_memory: "4GB"
    worker_pool_size: 2

monitoring:
  enabled: true
  metrics_port: 9090

logging:
  level: "info"
  format: "json"
  output: "stdout"

kubernetes:
  context: "staging"
  namespace: "provability-fabric-staging"
```

### Production Environment

```yaml
# config/environments/production.yaml
environment: production
debug: false

api:
  host: "0.0.0.0"
  port: 8080
  timeout: "60s"
  max_request_size: "50MB"
  cors:
    allowed_origins: ["https://provability-fabric.org", "https://api.provability-fabric.org"]

database:
  host: "postgresql-production.svc.cluster.local"
  port: 5432
  name: "provability_fabric_production"
  ssl_mode: "require"
  max_connections: 200
  connection_timeout: "15s"
  idle_timeout: "600s"

redis:
  host: "redis-production.svc.cluster.local"
  port: 6379
  password: "${REDIS_PASSWORD}"
  database: 0
  pool_size: 20

verification:
  lean:
    timeout: "300s"
    max_memory: "4GB"
    worker_pool_size: 8
  marabou:
    timeout: "600s"
    max_memory: "8GB"
    worker_pool_size: 4
  dryvr:
    timeout: "900s"
    max_memory: "16GB"
    worker_pool_size: 2

monitoring:
  enabled: true
  metrics_port: 9090
  health_check_port: 8081

logging:
  level: "warn"
  format: "json"
  output: "stdout"
  file:
    enabled: true
    path: "/var/log/provability-fabric"
    max_size: "100MB"
    max_age: "30d"
    max_backups: 30

kubernetes:
  context: "production"
  namespace: "provability-fabric"
  service_account: "provability-fabric-sa"
  image_pull_secrets: ["registry-secret"]
  resources:
    requests:
      cpu: "500m"
      memory: "1Gi"
    limits:
      cpu: "2"
      memory: "4Gi"
```

## Component-Specific Configuration

### API Configuration

```yaml
# config/api.yaml
server:
  host: "0.0.0.0"
  port: 8080
  read_timeout: "30s"
  write_timeout: "30s"
  idle_timeout: "120s"
  max_header_bytes: 1048576

middleware:
  cors:
    enabled: true
    allowed_origins: ["*"]
    allowed_methods: ["GET", "POST", "PUT", "DELETE", "OPTIONS"]
    allowed_headers: ["*"]
    exposed_headers: ["X-Total-Count"]
    allow_credentials: true
    max_age: 86400
  
  rate_limiting:
    enabled: true
    requests_per_minute: 100
    burst_size: 20
    key_by: "ip"  # ip, user, custom
  
  authentication:
    enabled: true
    methods: ["jwt", "api_key"]
    jwt:
      secret: "${JWT_SECRET}"
      expiration: "24h"
      refresh_expiration: "168h"
    api_key:
      header: "X-API-Key"
      prefix: "pf_"
  
  logging:
    enabled: true
    log_requests: true
    log_responses: false
    log_headers: false
    log_body: false

endpoints:
  health:
    path: "/health"
    timeout: "5s"
  metrics:
    path: "/metrics"
    timeout: "10s"
  docs:
    path: "/docs"
    enabled: true
  graphql:
    path: "/graphql"
    enabled: true
    playground: false
```

### Verification Engine Configuration

```yaml
# config/verification.yaml
engines:
  lean:
    enabled: true
    version: "4.0.0"
    timeout: "300s"
    max_memory: "2GB"
    worker_pool:
      size: 4
      queue_size: 100
      idle_timeout: "300s"
    options:
      max_heartbeats: 1000000
      max_search_depth: 1000
      max_steps: 1000000
  
  marabou:
    enabled: true
    version: "1.0.0"
    timeout: "600s"
    max_memory: "4GB"
    worker_pool:
      size: 2
      queue_size: 50
      idle_timeout: "600s"
    options:
      max_iterations: 10000
      tolerance: 1e-6
      verbosity: 0
  
  dryvr:
    enabled: true
    version: "1.0.0"
    timeout: "900s"
    max_memory: "8GB"
    worker_pool:
      size: 1
      queue_size: 25
      idle_timeout: "900s"
    options:
      max_time: 100.0
      max_steps: 1000
      tolerance: 1e-3

quality_gates:
  enabled: true
  lean:
    max_build_time: "180s"
    max_file_time: "60s"
    no_stale_sorry: true
    sorry_timeout: "48h"
  marabou:
    max_verification_time: "300s"
    min_accuracy: 0.95
  dryvr:
    max_reach_time: "600s"
    max_volume: 1000.0

caching:
  enabled: true
  ttl: "1h"
  max_size: 1000
  cleanup_interval: "10m"
```

### Monitoring Configuration

```yaml
# config/monitoring.yaml
metrics:
  enabled: true
  port: 9090
  path: "/metrics"
  collection_interval: "15s"
  
  custom_metrics:
    - name: "agent_requests_total"
      type: "counter"
      help: "Total number of agent requests"
      labels: ["agent", "method", "status"]
    
    - name: "proof_verification_duration"
      type: "histogram"
      help: "Proof verification duration"
      labels: ["agent", "proof_type", "status"]
      buckets: [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 30.0, 60.0]

health_checks:
  enabled: true
  port: 8081
  path: "/health"
  timeout: "5s"
  
  checks:
    - name: "database"
      type: "http"
      url: "http://localhost:8080/health/db"
      timeout: "3s"
      interval: "30s"
    
    - name: "redis"
      type: "http"
      url: "http://localhost:8080/health/redis"
      timeout: "3s"
      interval: "30s"
    
    - name: "verification_engines"
      type: "http"
      url: "http://localhost:8080/health/verification"
      timeout: "5s"
      interval: "60s"

alerting:
  enabled: true
  rules:
    - alert: "HighErrorRate"
      expr: "rate(agent_requests_total{status=~\"5..\"}[5m]) > 0.1"
      for: "2m"
      labels:
        severity: "warning"
      annotations:
        summary: "High error rate detected"
        description: "Error rate is {{ $value }} errors per second"
    
    - alert: "HighLatency"
      expr: "histogram_quantile(0.95, proof_verification_duration_seconds) > 30"
      for: "2m"
      labels:
        severity: "warning"
      annotations:
        summary: "High verification latency"
        description: "P95 verification latency is {{ $value }} seconds"
    
    - alert: "VerificationFailure"
      expr: "rate(proof_verification_total{status=\"failure\"}[5m]) > 0"
      for: "1m"
      labels:
        severity: "critical"
      annotations:
        summary: "Proof verification failures detected"
        description: "Verification is failing at {{ $value }} failures per second"

dashboards:
  enabled: true
  grafana:
    url: "http://grafana:3000"
    api_key: "${GRAFANA_API_KEY}"
    organization: "provability-fabric"
    
  default_dashboards:
    - name: "Provability-Fabric Overview"
      uid: "provability-fabric-overview"
      folder: "Provability-Fabric"
    
    - name: "Agent Performance"
      uid: "agent-performance"
      folder: "Provability-Fabric"
    
    - name: "Verification Engine Status"
      uid: "verification-engine-status"
      folder: "Provability-Fabric"
```

### Security Configuration

```yaml
# config/security.yaml
authentication:
  enabled: true
  methods: ["jwt", "api_key", "oauth2"]
  
  jwt:
    secret: "${JWT_SECRET}"
    algorithm: "HS256"
    expiration: "24h"
    refresh_expiration: "168h"
    issuer: "provability-fabric"
    audience: "provability-fabric-users"
  
  api_key:
    enabled: true
    header: "X-API-Key"
    prefix: "pf_"
    rotation_enabled: true
    rotation_interval: "90d"
  
  oauth2:
    enabled: true
    providers:
      google:
        client_id: "${GOOGLE_CLIENT_ID}"
        client_secret: "${GOOGLE_CLIENT_SECRET}"
        redirect_url: "https://api.provability-fabric.org/auth/callback/google"
      github:
        client_id: "${GITHUB_CLIENT_ID}"
        client_secret: "${GITHUB_CLIENT_SECRET}"
        redirect_url: "https://api.provability-fabric.org/auth/callback/github"

authorization:
  enabled: true
  rbac:
    enabled: true
    default_role: "user"
    
  roles:
    admin:
      permissions: ["*"]
      description: "Full system access"
    
    developer:
      permissions: ["agent:read", "agent:write", "proof:read", "proof:write"]
      description: "Agent and proof management"
    
    operator:
      permissions: ["agent:read", "deployment:read", "deployment:write", "monitoring:read"]
      description: "Deployment and monitoring"
    
    user:
      permissions: ["agent:read", "proof:read"]
      description: "Read-only access"

encryption:
  enabled: true
  algorithm: "AES-256-GCM"
  key: "${ENCRYPTION_KEY}"
  key_rotation:
    enabled: true
    interval: "90d"
    grace_period: "7d"
  
  at_rest:
    enabled: true
    algorithm: "AES-256-XTS"
  
  in_transit:
    enabled: true
    tls:
      version: "1.3"
      min_version: "1.2"
      cipher_suites: ["TLS_AES_256_GCM_SHA384", "TLS_CHACHA20_POLY1305_SHA256"]

network_security:
  enabled: true
  firewall:
    enabled: true
    rules:
      - action: "allow"
        source: "0.0.0.0/0"
        destination: "0.0.0.0/0"
        protocol: "tcp"
        port: 8080
        description: "API access"
      
      - action: "deny"
        source: "0.0.0.0/0"
        destination: "0.0.0.0/0"
        protocol: "tcp"
        port: 22
        description: "SSH access"
  
  tls:
    enabled: true
    certificate: "${TLS_CERT}"
    private_key: "${TLS_KEY}"
    ca_certificate: "${CA_CERT}"
    client_auth: "request"
```

## Environment Variables

### Core Environment Variables

```bash
# API Configuration
export PF_API_HOST="0.0.0.0"
export PF_API_PORT="8080"
export PF_API_TIMEOUT="30s"
export PF_API_MAX_REQUEST_SIZE="10MB"

# Database Configuration
export PF_DB_HOST="localhost"
export PF_DB_PORT="5432"
export PF_DB_NAME="provability_fabric"
export PF_DB_USERNAME="provability_fabric"
export PF_DB_PASSWORD="secure_password"
export PF_DB_SSL_MODE="require"

# Redis Configuration
export PF_REDIS_HOST="localhost"
export PF_REDIS_PORT="6379"
export PF_REDIS_PASSWORD="redis_password"
export PF_REDIS_DATABASE="0"

# Verification Engine Configuration
export PF_LEAN_TIMEOUT="300s"
export PF_LEAN_MAX_MEMORY="2GB"
export PF_MARABOU_TIMEOUT="600s"
export PF_MARABOU_MAX_MEMORY="4GB"
export PF_DRYVR_TIMEOUT="900s"
export PF_DRYVR_MAX_MEMORY="8GB"

# Security Configuration
export PF_JWT_SECRET="your-super-secret-jwt-key"
export PF_ENCRYPTION_KEY="your-32-byte-encryption-key"
export PF_TLS_CERT="/path/to/cert.pem"
export PF_TLS_KEY="/path/to/key.pem"

# Monitoring Configuration
export PF_METRICS_PORT="9090"
export PF_HEALTH_CHECK_PORT="8081"
export PF_LOG_LEVEL="info"
export PF_LOG_FORMAT="json"

# Kubernetes Configuration
export PF_K8S_CONTEXT="default"
export PF_K8S_NAMESPACE="provability-fabric"
export PF_K8S_SERVICE_ACCOUNT="default"
```

### Environment-Specific Variables

```bash
# Development
export PF_ENVIRONMENT="development"
export PF_DEBUG="true"
export PF_LOG_LEVEL="debug"
export PF_LOG_FORMAT="text"

# Staging
export PF_ENVIRONMENT="staging"
export PF_DEBUG="false"
export PF_LOG_LEVEL="info"
export PF_LOG_FORMAT="json"

# Production
export PF_ENVIRONMENT="production"
export PF_DEBUG="false"
export PF_LOG_LEVEL="warn"
export PF_LOG_FORMAT="json"
export PF_METRICS_ENABLED="true"
export PF_ALERTING_ENABLED="true"
```

## Configuration Validation

### Validation Commands

```bash
# Validate main configuration
pf config validate

# Validate specific configuration file
pf config validate --file config/production.yaml

# Validate with strict mode
pf config validate --strict

# Validate specific components
pf config validate --component api
pf config validate --component verification
pf config validate --component security
```

### Validation Rules

```yaml
# config/validation-rules.yaml
rules:
  api:
    required_fields: ["host", "port", "timeout"]
    port_range: [1, 65535]
    timeout_range: ["1s", "300s"]
  
  database:
    required_fields: ["type", "host", "port", "name"]
    supported_types: ["postgresql", "mysql", "sqlite"]
    port_range: [1, 65535]
  
  verification:
    lean:
      required_fields: ["timeout", "max_memory", "worker_pool_size"]
      timeout_range: ["30s", "600s"]
      max_memory_range: ["512MB", "8GB"]
      worker_pool_size_range: [1, 16]
    
    marabou:
      required_fields: ["timeout", "max_memory", "worker_pool_size"]
      timeout_range: ["60s", "1200s"]
      max_memory_range: ["1GB", "16GB"]
      worker_pool_size_range: [1, 8]
  
  security:
    jwt:
      required_fields: ["secret", "expiration"]
      secret_min_length: 32
      expiration_range: ["1h", "168h"]
    
    encryption:
      required_fields: ["key", "algorithm"]
      key_min_length: 32
      supported_algorithms: ["AES-256-GCM", "ChaCha20-Poly1305"]
```

## Configuration Management

### Configuration Updates

```bash
# Update configuration value
pf config set api.port 9090

# Get configuration value
pf config get api.port

# List all configuration
pf config list

# Export configuration
pf config export config.yaml

# Import configuration
pf config import config.yaml
```

### Configuration Migration

```bash
# Check for configuration changes
pf config migrate --check

# Migrate configuration to new version
pf config migrate --to-version 2.0.0

# Rollback configuration migration
pf config migrate --rollback
```

## Best Practices

### Configuration Organization

1. **Use environment-specific files** - Separate configurations for different environments
2. **Centralize sensitive data** - Use environment variables for secrets
3. **Validate configurations** - Always validate before deployment
4. **Version control** - Track configuration changes in version control
5. **Documentation** - Document all configuration options and their effects

### Security Considerations

1. **Never commit secrets** - Use environment variables or external secret management
2. **Rotate keys regularly** - Implement automatic key rotation
3. **Limit access** - Restrict configuration access to authorized personnel
4. **Audit changes** - Log all configuration modifications
5. **Test security** - Regularly test security configurations

### Performance Optimization

1. **Resource limits** - Set appropriate resource limits for all components
2. **Connection pooling** - Configure database and Redis connection pools
3. **Caching** - Enable caching where appropriate
4. **Worker pools** - Configure verification engine worker pools
5. **Monitoring** - Enable comprehensive monitoring and alerting

## Conclusion

Effective configuration management is crucial for successful Provability-Fabric deployments. Key principles include:

- **Environment separation** - Different configurations for different environments
- **Security first** - Secure handling of sensitive configuration data
- **Validation** - Always validate configurations before use
- **Documentation** - Comprehensive documentation of all options
- **Automation** - Automated configuration management and deployment

For more information about specific configuration options, refer to the relevant documentation sections or use the CLI help commands.
