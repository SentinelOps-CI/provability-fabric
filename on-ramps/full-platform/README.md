# Full Platform On-Ramp

The Full Platform on-ramp provides comprehensive Provability Fabric capabilities including sidecar integration, epochs management, Information Flow Control (IFC), and deterministic egress handling.

## Overview

This on-ramp includes everything from previous on-ramps plus:
- **Sidecar Integration**: Runtime policy enforcement
- **Epoch Management**: Permission revocation safety
- **Information Flow Control**: Fine-grained data access control
- **Deterministic Egress**: Controlled external communications
- **Advanced Runtime**: MPC fintech, privacy controls, RAG guards

## Quick Start

### 1. Deploy Full Platform

```bash
# Clone the repository
git clone https://github.com/SentinelOps-CI/provability-fabric
cd provability-fabric

# Deploy with Docker Compose
docker compose up -d --build

# Verify deployment
so deploy --epoch stable
```

### 2. Configure Sidecar Integration

Create `config/sidecar-config.yaml`:

```yaml
sidecar:
  enabled: true
  image: provability-fabric/sidecar-watcher:latest
  
  # Policy enforcement
  policy:
    enforcement_mode: "strict"
    fallback_action: "deny"
    audit_logging: true
    
  # Epoch management
  epoch:
    current: 42
    rotation_policy: "automatic"
    grace_period_ms: 5000
    
  # Information Flow Control
  ifc:
    enabled: true
    declassification_policy: "strict"
    label_propagation: true
    
  # Deterministic egress
  egress:
    enabled: true
    allowed_endpoints:
      - "api.example.com"
      - "database.internal"
    rate_limiting: true
```

### 3. Deploy Application with Sidecar

```yaml
# k8s-app-with-sidecar.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app-with-sidecar
spec:
  replicas: 3
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
        provability-fabric.io/sidecar: "enabled"
      annotations:
        provability-fabric.io/policy: "security-policy"
        provability-fabric.io/epoch: "42"
    spec:
      containers:
      - name: my-app
        image: my-app:latest
        ports:
        - containerPort: 8080
        
      - name: sidecar-watcher
        image: provability-fabric/sidecar-watcher:latest
        env:
        - name: POLICY_HASH
          value: "sha256:abc123..."
        - name: EPOCH
          value: "42"
        volumeMounts:
        - name: policy-config
          mountPath: /etc/provability-fabric
      volumes:
      - name: policy-config
        configMap:
          name: sidecar-policy-config
```

### 4. Enable Advanced Features

```bash
# Enable MPC fintech capabilities
so deploy --feature mpc-fintech --epoch rotate

# Configure privacy controls
so deploy --feature privacy --config privacy-config.yaml

# Set up RAG guards
so deploy --feature rag-guard --config rag-config.yaml
```

## Features

### Sidecar Integration
- **Runtime Enforcement**: Real-time policy enforcement
- **Permission Monitoring**: Track access patterns
- **Audit Logging**: Comprehensive activity logs
- **Hot Reloading**: Update policies without restarts

### Epoch Management
- **Automatic Rotation**: Scheduled epoch transitions
- **Revocation Safety**: Safe permission revocation
- **Grace Periods**: Smooth transitions
- **Rollback Support**: Emergency rollback capabilities

### Information Flow Control
- **Data Labeling**: Automatic data classification
- **Declassification Policies**: Controlled data downgrading
- **Label Propagation**: Automatic label inheritance
- **Access Control**: Fine-grained permissions

### Deterministic Egress
- **Endpoint Control**: Whitelist external communications
- **Rate Limiting**: Prevent abuse and ensure determinism
- **Audit Trails**: Complete external communication logs
- **Policy Enforcement**: Block unauthorized external calls

## Configuration

### Sidecar Configuration

```yaml
# sidecar-config.yaml
sidecar:
  # Runtime settings
  runtime:
    enforcement_mode: "strict"  # strict|permissive|audit
    fallback_action: "deny"     # deny|allow|log
    audit_logging: true
    
  # Policy management
  policy:
    source: "configmap"         # configmap|file|api
    hot_reload: true
    validation: true
    
  # Epoch configuration
  epoch:
    current: 42
    rotation_policy: "automatic" # automatic|manual|scheduled
    grace_period_ms: 5000
    rollback_enabled: true
    
  # IFC settings
  ifc:
    enabled: true
    declassification_policy: "strict" # strict|permissive|disabled
    label_propagation: true
    default_label: "confidential"
    
  # Egress control
  egress:
    enabled: true
    allowed_endpoints:
      - "api.example.com:443"
      - "database.internal:5432"
    rate_limiting:
      enabled: true
      requests_per_minute: 1000
    audit_logging: true
```

### Advanced Features

#### MPC Fintech

```yaml
# mpc-fintech-config.yaml
mpc_fintech:
  enabled: true
  participants:
    - name: "bank-a"
      endpoint: "https://bank-a.example.com"
      public_key: "-----BEGIN PUBLIC KEY-----..."
    - name: "bank-b"
      endpoint: "https://bank-b.example.com"
      public_key: "-----BEGIN PUBLIC KEY-----..."
  
  protocols:
    - name: "secure-sum"
      threshold: 2
      timeout_ms: 30000
    - name: "private-equality"
      threshold: 3
      timeout_ms: 45000
```

#### Privacy Controls

```yaml
# privacy-config.yaml
privacy:
  enabled: true
  
  # Differential privacy
  differential_privacy:
    enabled: true
    epsilon: 1.0
    delta: 1e-5
    
  # Homomorphic encryption
  homomorphic_encryption:
    enabled: true
    scheme: "bfv"
    poly_modulus_degree: 4096
    
  # Secure multi-party computation
  smpc:
    enabled: true
    protocol: "spdz"
    threshold: 2
```

#### RAG Guards

```yaml
# rag-guard-config.yaml
rag_guard:
  enabled: true
  
  # Content filtering
  content_filtering:
    enabled: true
    categories:
      - "sensitive"
      - "confidential"
      - "pii"
    
  # Semantic analysis
  semantic_analysis:
    enabled: true
    model: "sentence-transformers/all-MiniLM-L6-v2"
    similarity_threshold: 0.8
    
  # Access control
  access_control:
    enabled: true
    policies:
      - role: "admin"
        allowed_operations: ["read", "write", "delete"]
      - role: "user"
        allowed_operations: ["read"]
```

## Integration Examples

### Kubernetes Admission Controller

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: admission-controller-config
data:
  config.yaml: |
    admission:
      enabled: true
      webhook:
        url: "https://admission-controller.provability-fabric.svc.cluster.local"
        ca_bundle: "..."
      
    policies:
      - name: "security-policy"
        namespace: "production"
        enforcement: "strict"
        
    sidecar:
      auto_inject: true
      selector:
        matchLabels:
          provability-fabric.io/sidecar: "enabled"
```

### Service Mesh Integration

```yaml
# istio-sidecar-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-sidecar-config
data:
  sidecar.istio.io/proxyImage: "provability-fabric/sidecar-watcher:latest"
  sidecar.istio.io/userVolume: '{"name":"policy-config","configMap":{"name":"sidecar-policy"}}'
  sidecar.istio.io/userVolumeMount: '{"name":"policy-config","mountPath":"/etc/provability-fabric"}'
```

## Monitoring and Observability

### Metrics

```bash
# View runtime metrics
so metrics --namespace production

# Check epoch status
so epoch status

# Monitor sidecar health
so sidecar health --namespace production
```

### Logs

```bash
# View sidecar logs
so logs sidecar --namespace production --follow

# Check policy enforcement logs
so logs policy --namespace production --level debug

# Monitor egress activity
so logs egress --namespace production --follow
```

### Alerts

```yaml
# prometheus-alerts.yaml
groups:
- name: provability-fabric
  rules:
  - alert: PolicyViolation
    expr: provability_fabric_policy_violations_total > 0
    for: 1m
    labels:
      severity: warning
    annotations:
      summary: "Policy violation detected"
      
  - alert: EpochRotationFailed
    expr: provability_fabric_epoch_rotation_failures_total > 0
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "Epoch rotation failed"
```

## Migration Path

This is the complete platform. Teams can:

1. **Customize Features**: Enable/disable specific capabilities
2. **Scale Horizontally**: Add more sidecars and enforcement points
3. **Integrate Ecosystem**: Connect with external compliance tools
4. **Develop Extensions**: Build custom policy engines and validators

## Support

- Documentation: [docs/](../../docs/)
- Architecture: [docs/architecture.md](../../docs/architecture.md)
- Runtime Components: [runtime/](../../runtime/)
- Examples: [examples/full-platform/](../examples/)
- CLI Reference: [docs/cli-reference.md](../../docs/cli-reference.md)
