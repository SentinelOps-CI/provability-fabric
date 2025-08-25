# Deployment Guide

This guide covers production deployment of Provability-Fabric applications, including environment setup, configuration, monitoring, and maintenance.

## Deployment Overview

### Deployment Architecture

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Load Balancer │    │  Ingress Proxy  │    │  Agent Pods     │
│                 │    │                 │    │                 │
│   - SSL/TLS     │───▶│   - Routing     │───▶│   - Sidecar     │
│   - Rate Limit  │    │   - Auth        │    │   - Monitoring  │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### Deployment Phases

1. **Environment Setup** - Infrastructure and dependencies
2. **Configuration** - Environment-specific settings
3. **Deployment** - Application deployment
4. **Verification** - Health checks and testing
5. **Monitoring** - Runtime monitoring and alerting

## Environment Setup

### Prerequisites

- **Kubernetes Cluster** - v1.24+ with sufficient resources
- **Container Registry** - For storing agent images
- **Database** - PostgreSQL or similar for persistence
- **Monitoring Stack** - Prometheus, Grafana, etc.
- **Load Balancer** - For external access

### Infrastructure Requirements

```yaml
# infrastructure/requirements.yaml
kubernetes:
  version: "1.24+"
  nodes:
    control_plane: 3
    workers: 5
  resources:
    cpu: "8 cores per node"
    memory: "32GB per node"
    storage: "100GB per node"

database:
  type: "PostgreSQL"
  version: "14+"
  resources:
    cpu: "4 cores"
    memory: "16GB"
    storage: "500GB"

monitoring:
  prometheus: true
  grafana: true
  alertmanager: true
  storage: "100GB"
```

### Cluster Setup

```bash
# Create cluster using kind (development)
kind create cluster --name provability-fabric --config kind-config.yaml

# Or using k3s (production)
curl -sfL https://get.k3s.io | INSTALL_K3S_EXEC="--write-kubeconfig-mode=644" sh -

# Verify cluster
kubectl cluster-info
kubectl get nodes
```

## Configuration Management

### Environment Configuration

```yaml
# config/environments/production.yaml
environment: production
domain: "api.provability-fabric.org"

database:
  host: "postgresql.production.svc.cluster.local"
  port: 5432
  name: "provability_fabric_prod"
  ssl_mode: "require"

redis:
  host: "redis.production.svc.cluster.local"
  port: 6379
  password: "${REDIS_PASSWORD}"

monitoring:
  prometheus_url: "http://prometheus.monitoring.svc.cluster.local:9090"
  grafana_url: "http://grafana.monitoring.svc.cluster.local:3000"

security:
  jwt_secret: "${JWT_SECRET}"
  encryption_key: "${ENCRYPTION_KEY}"
  tls_cert: "${TLS_CERT}"
  tls_key: "${TLS_KEY}"
```

### Secrets Management

```bash
# Create Kubernetes secrets
kubectl create secret generic db-credentials \
  --from-literal=username=provability_fabric \
  --from-literal=password=$(openssl rand -base64 32)

kubectl create secret generic api-keys \
  --from-literal=jwt_secret=$(openssl rand -base64 64) \
  --from-literal=encryption_key=$(openssl rand -base64 32)

kubectl create secret tls api-tls \
  --cert=ssl/cert.pem \
  --key=ssl/key.pem
```

### ConfigMaps

```yaml
# config/configmaps/app-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: app-config
  namespace: provability-fabric
data:
  LOG_LEVEL: "info"
  API_VERSION: "v1"
  DEFAULT_TIMEOUT: "30s"
  MAX_REQUEST_SIZE: "10MB"
  
  # Feature flags
  ENABLE_GRAPHQL: "true"
  ENABLE_WEBSOCKETS: "true"
  ENABLE_RATE_LIMITING: "true"
  
  # Verification settings
  LEAN_TIMEOUT: "300s"
  MARABOU_TIMEOUT: "600s"
  DRYVR_TIMEOUT: "900s"
```

## Application Deployment

### Core Services

```yaml
# deployments/core-services.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: provability-fabric-api
  namespace: provability-fabric
spec:
  replicas: 3
  selector:
    matchLabels:
      app: provability-fabric-api
  template:
    metadata:
      labels:
        app: provability-fabric-api
    spec:
      containers:
      - name: api
        image: provability-fabric/api:latest
        ports:
        - containerPort: 8080
        env:
        - name: LOG_LEVEL
          valueFrom:
            configMapKeyRef:
              name: app-config
              key: LOG_LEVEL
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-credentials
              key: url
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
```

### Agent Deployments

```yaml
# deployments/agents/text-generator.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: text-generator
  namespace: agents
  labels:
    app: text-generator
    provability-fabric.io/agent: "true"
spec:
  replicas: 3
  selector:
    matchLabels:
      app: text-generator
  template:
    metadata:
      labels:
        app: text-generator
        provability-fabric.io/agent: "true"
      annotations:
        provability-fabric.io/sidecar: "true"
        provability-fabric.io/proof-bundle: "text-generator-v1.0.0"
    spec:
      initContainers:
      - name: proof-verification
        image: provability-fabric/verifier:latest
        command: ["/bin/sh", "-c"]
        args:
        - |
          pf verify --bundle text-generator-v1.0.0
          if [ $? -eq 0 ]; then
            echo "Proof verification passed"
            exit 0
          else
            echo "Proof verification failed"
            exit 1
          fi
      containers:
      - name: text-generator
        image: text-generator:1.0.0
        ports:
        - containerPort: 8080
        env:
        - name: MAX_LENGTH
          value: "1000"
        - name: CONTENT_FILTER
          value: "true"
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "200m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
      - name: sidecar-watcher
        image: provability-fabric/sidecar-watcher:latest
        env:
        - name: AGENT_NAME
          value: "text-generator"
        - name: MONITORING_ENDPOINT
          value: "http://monitoring.provability-fabric.svc.cluster.local:8080"
        resources:
          requests:
            memory: "64Mi"
            cpu: "50m"
          limits:
            memory: "128Mi"
            cpu: "100m"
```

### Services and Ingress

```yaml
# services/api-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: provability-fabric-api
  namespace: provability-fabric
spec:
  selector:
    app: provability-fabric-api
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: ClusterIP

---
# ingress/api-ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: api-ingress
  namespace: provability-fabric
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/rate-limit: "100"
    nginx.ingress.kubernetes.io/rate-limit-window: "1m"
spec:
  tls:
  - hosts:
    - api.provability-fabric.org
    secretName: api-tls
  rules:
  - host: api.provability-fabric.org
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: provability-fabric-api
            port:
              number: 80
```

## Monitoring and Observability

### Metrics Collection

```yaml
# monitoring/prometheus-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: prometheus-config
  namespace: monitoring
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
      evaluation_interval: 15s
    
    scrape_configs:
    - job_name: 'provability-fabric-api'
      static_configs:
      - targets: ['provability-fabric-api.provability-fabric.svc.cluster.local:8080']
      metrics_path: /metrics
      scrape_interval: 5s
    
    - job_name: 'agents'
      kubernetes_sd_configs:
      - role: pod
        namespaces:
          names:
          - agents
      relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_provability_fabric_io_agent]
        regex: "true"
        action: keep
      - source_labels: [__address__]
        target_label: __metrics_path__
        replacement: /metrics
```

### Grafana Dashboards

```json
{
  "dashboard": {
    "title": "Provability-Fabric Overview",
    "panels": [
      {
        "title": "API Requests per Second",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{method}} {{endpoint}}"
          }
        ]
      },
      {
        "title": "Agent Response Time",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P95 Response Time"
          }
        ]
      },
      {
        "title": "Proof Verification Success Rate",
        "type": "stat",
        "targets": [
          {
            "expr": "rate(proof_verification_total{status=\"success\"}[5m]) / rate(proof_verification_total[5m]) * 100",
            "legendFormat": "Success Rate %"
          }
        ]
      }
    ]
  }
}
```

### Alerting Rules

```yaml
# monitoring/alertmanager-rules.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: provability-fabric-alerts
  namespace: monitoring
spec:
  groups:
  - name: provability-fabric
    rules:
    - alert: HighErrorRate
      expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.1
      for: 2m
      labels:
        severity: warning
      annotations:
        summary: "High error rate detected"
        description: "Error rate is {{ $value }} errors per second"
    
    - alert: HighLatency
      expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1
      for: 2m
      labels:
        severity: warning
      annotations:
        summary: "High latency detected"
        description: "P95 latency is {{ $value }} seconds"
    
    - alert: ProofVerificationFailure
      expr: rate(proof_verification_total{status=\"failure\"}[5m]) > 0
      for: 1m
      labels:
        severity: critical
      annotations:
        summary: "Proof verification failures detected"
        description: "Proof verification is failing at {{ $value }} failures per second"
```

## Deployment Automation

### CI/CD Pipeline

```yaml
# .github/workflows/deploy.yml
name: Deploy to Production

on:
  push:
    branches: [main]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Configure kubectl
      uses: azure/setup-kubectl@v3
      with:
        version: 'latest'
    
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v3
    
    - name: Build and push images
      run: |
        docker buildx build --platform linux/amd64,linux/arm64 \
          -t provability-fabric/api:${{ github.sha }} \
          -t provability-fabric/api:latest \
          --push .
    
    - name: Deploy to production
      run: |
        kubectl config use-context production
        kubectl apply -f k8s/
        kubectl rollout status deployment/provability-fabric-api
    
    - name: Verify deployment
      run: |
        kubectl get pods -n provability-fabric
        kubectl get services -n provability-fabric
        kubectl get ingress -n provability-fabric
    
    - name: Run smoke tests
      run: |
        ./scripts/smoke-tests.sh production
```

### Deployment Scripts

```bash
#!/bin/bash
# scripts/deploy.sh

set -e

ENVIRONMENT=$1
VERSION=$2

if [ -z "$ENVIRONMENT" ] || [ -z "$VERSION" ]; then
    echo "Usage: $0 <environment> <version>"
    exit 1
fi

echo "Deploying version $VERSION to $ENVIRONMENT..."

# Update image tags
kubectl set image deployment/provability-fabric-api \
    api=provability-fabric/api:$VERSION \
    -n provability-fabric

# Wait for rollout
kubectl rollout status deployment/provability-fabric-api \
    -n provability-fabric \
    --timeout=300s

# Verify deployment
kubectl get pods -n provability-fabric
kubectl get services -n provability-fabric

echo "Deployment completed successfully!"
```

## Security Considerations

### Network Policies

```yaml
# security/network-policies.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: default-deny
  namespace: provability-fabric
spec:
  podSelector: {}
  policyTypes:
  - Ingress
  - Egress

---
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: allow-api-access
  namespace: provability-fabric
spec:
  podSelector:
    matchLabels:
      app: provability-fabric-api
  policyTypes:
  - Ingress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: ingress-nginx
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: database
    ports:
    - protocol: TCP
      port: 5432
```

### RBAC Configuration

```yaml
# security/rbac.yaml
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: provability-fabric-agent
rules:
- apiGroups: [""]
  resources: ["pods", "services", "configmaps", "secrets"]
  verbs: ["get", "list", "watch"]
- apiGroups: ["apps"]
  resources: ["deployments", "replicasets"]
  verbs: ["get", "list", "watch"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: provability-fabric-agent
subjects:
- kind: ServiceAccount
  name: agent-sa
  namespace: agents
roleRef:
  kind: ClusterRole
  name: provability-fabric-agent
  apiGroup: rbac.authorization.k8s.io
```

## Maintenance and Updates

### Rolling Updates

```bash
# Perform rolling update
kubectl rollout restart deployment/provability-fabric-api -n provability-fabric

# Monitor update progress
kubectl rollout status deployment/provability-fabric-api -n provability-fabric

# Rollback if needed
kubectl rollout undo deployment/provability-fabric-api -n provability-fabric
```

### Backup and Recovery

```bash
#!/bin/bash
# scripts/backup.sh

BACKUP_DIR="/backups/$(date +%Y%m%d_%H%M%S)"
mkdir -p $BACKUP_DIR

# Backup database
pg_dump $DATABASE_URL > $BACKUP_DIR/database.sql

# Backup Kubernetes resources
kubectl get all -n provability-fabric -o yaml > $BACKUP_DIR/k8s-resources.yaml

# Backup configuration
kubectl get configmaps,secrets -n provability-fabric -o yaml > $BACKUP_DIR/config.yaml

echo "Backup completed: $BACKUP_DIR"
```

### Health Checks

```bash
#!/bin/bash
# scripts/health-check.sh

# Check API health
API_HEALTH=$(curl -s -o /dev/null -w "%{http_code}" https://api.provability-fabric.org/health)
if [ "$API_HEALTH" != "200" ]; then
    echo "API health check failed: $API_HEALTH"
    exit 1
fi

# Check database connectivity
DB_STATUS=$(kubectl exec -n provability-fabric deployment/provability-fabric-api -- pg_isready -h postgresql)
if [ $? -ne 0 ]; then
    echo "Database connectivity check failed"
    exit 1
fi

# Check agent status
AGENT_STATUS=$(kubectl get pods -n agents -l provability-fabric.io/agent=true --field-selector=status.phase!=Running)
if [ -n "$AGENT_STATUS" ]; then
    echo "Some agents are not running properly"
    echo "$AGENT_STATUS"
    exit 1
fi

echo "All health checks passed"
```

## Conclusion

Successful production deployment requires:

1. **Proper Planning** - Infrastructure and resource planning
2. **Security First** - Network policies, RBAC, and secrets management
3. **Monitoring** - Comprehensive observability and alerting
4. **Automation** - CI/CD pipelines and deployment scripts
5. **Maintenance** - Regular updates, backups, and health checks

For more deployment examples, see the [Examples](examples.md) document.
