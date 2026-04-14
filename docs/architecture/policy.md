# Policy Enforcement System Documentation

This document provides comprehensive documentation for the Provability Fabric policy enforcement system, covering Attribute-Based Access Control (ABAC), Information Flow Control (IFC), and unified action management.

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Policy Model](#policy-model)
4. [ABAC (Attribute-Based Access Control)](#abac)
5. [IFC (Information Flow Control)](#ifc)
6. [Unified Actions](#unified-actions)
7. [Policy Enforcement](#policy-enforcement)
8. [Monitoring and Alerting](#monitoring-and-alerting)
9. [Operational Procedures](#operational-procedures)
10. [Troubleshooting](#troubleshooting)

## Overview

The Provability Fabric policy enforcement system provides a unified, secure, and auditable way to manage access control across tools, documents, and operations. The system combines:

- **ABAC**: Dynamic access control based on user attributes, context, and resource properties
- **IFC**: Information flow control to prevent unauthorized data disclosure
- **Unified Actions**: Consistent permission model across all system operations
- **Formal Verification**: Mathematical proofs of security properties
- **Runtime Enforcement**: Real-time policy enforcement with comprehensive auditing

### Key Features

- **Unified Permission Model**: Single `permitD` function for all access decisions
- **Field-Level Access Control**: Granular control over document fields and paths
- **Epoch-Based Revocation**: Time-bounded permissions with automatic expiration
- **Witness Validation**: Cryptographic verification of access paths
- **Bridge Guarantees**: Formal connection between local checks and global properties

## Architecture

### System Components

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Policy DSL    │    │   Lean Proofs   │    │   DFA Export    │
│                 │    │                 │    │                 │
│ - Grammar       │───▶│ - Permit        │───▶│ - State Machine │
│ - ABAC Rules    │    │ - permitD       │    │ - Transitions   │
│ - IFC Rules     │    │ - Soundness     │    │ - Rate Limits   │
└─────────────────┘    └─────────────────┘    └─────────────────┘
                                │
                                ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│  Sidecar       │    │   Policy        │    │   NI Monitor    │
│  Watcher       │    │   Adapter       │    │                 │
│                 │    │                 │    │                 │
│ - Event        │◀───│ - Principal     │◀───│ - Label Flow    │
│   Processing   │    │   Mapping       │    │ - Declass Rules │
│ - Enforcement  │    │ - Context       │    │ - Bridge        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### Data Flow

1. **Policy Definition**: Policies written in DSL, compiled to Lean for verification
2. **Proof Generation**: Formal proofs establish security properties
3. **DFA Export**: Deterministic finite automata generated for runtime use
4. **Runtime Enforcement**: Sidecar enforces policies using `permitD` function
5. **Audit Trail**: All decisions logged with cryptographic evidence

## Policy Model

### Core Concepts

#### Principal
Represents a user, service, or agent with:
- **ID**: Unique identifier
- **Roles**: List of assigned roles
- **Organization**: Organizational context
- **Attributes**: Dynamic key-value pairs

```yaml
principal:
  id: "user123"
  roles: ["reader", "email_user"]
  org: "engineering"
  attributes:
    project: "alpha"
    clearance: "internal"
    location: "us-west"
```

#### Action
Unified representation of all operations:
- **Call**: Tool/service invocation
- **Read**: Document field access
- **Write**: Document field modification
- **Grant**: Permission delegation

```yaml
action:
  type: "read"
  resource:
    doc_id: "doc://team/project"
    path: ["data", "requirements"]
  context:
    session: "sess_456"
    epoch: 5
    timestamp: 1640995200
```

#### Context
Runtime information for access decisions:
- **Session**: Unique session identifier
- **Epoch**: Permission snapshot version
- **Attributes**: Dynamic context attributes
- **Tenant**: Multi-tenancy isolation
- **Timestamp**: Temporal access control

### Permission Evaluation

The core permission function `permitD` evaluates:

```lean
def permitD (u : Principal) (a : Action) (γ : Ctx) : Bool :=
  match a with
  | Action.Call tool => checkToolAccess u tool γ
  | Action.Read doc path => checkReadAccess u doc path γ
  | Action.Write doc path => checkWriteAccess u doc path γ
  | Action.Grant target action => checkGrantAccess u target action γ
```

## ABAC (Attribute-Based Access Control)

### Attribute Types

#### User Attributes
- **Static**: Role, organization, clearance level
- **Dynamic**: Project assignment, location, time of day
- **Session**: Current session context, authentication method

#### Resource Attributes
- **Document**: Owner, classification, sensitivity level
- **Field**: Path, data type, access restrictions
- **Tool**: Capability, rate limits, cost implications

#### Environment Attributes
- **Time**: Current time, business hours, maintenance windows
- **Location**: Geographic location, network segment
- **Risk**: Current threat level, incident status

### ABAC Rules

#### Basic Rules
```yaml
# Allow access based on role and project
allow:
  role: "developer"
  resource: "project_alpha"
  condition: "attr(project) == 'alpha'"

# Deny access outside business hours
deny:
  role: "any"
  resource: "any"
  condition: "time.hour < 9 OR time.hour > 17"
```

#### Advanced Rules
```yaml
# Conditional access based on multiple attributes
allow:
  role: "manager"
  resource: "sensitive_data"
  condition: |
    attr(clearance) >= "confidential" AND
    attr(project) == resource.project AND
    session.location == "secure_facility"

# Rate-limited access
allow:
  role: "api_user"
  resource: "external_api"
  condition: "rate_limit('api_calls', 100, '1h')"
```

### Attribute Evaluation

Attributes are evaluated using a flexible expression language:

```yaml
# String comparison
attr(project) == "alpha"

# Numeric comparison
attr(clearance_level) >= 3

# Set membership
attr(location) in ["us-west", "us-east"]

# Time ranges
time.epoch in [1640995200, 1641081600]

# Complex conditions
(attr(role) == "admin") OR 
(attr(project) == resource.project AND attr(clearance) >= resource.sensitivity)
```

## IFC (Information Flow Control)

### Label System

#### Security Labels
- **Public**: No restrictions, accessible to all
- **Internal**: Company-wide access
- **Confidential**: Restricted to specific groups
- **Secret**: Highly restricted access
- **Custom**: Organization-specific classifications

#### Label Lattice
```
    Secret
      │
  Confidential
      │
    Internal
      │
     Public
```

### Flow Control Rules

#### Basic Flow Rules
```yaml
# Information can flow from lower to higher labels
flows:
  - from: "Public"
    to: ["Internal", "Confidential", "Secret"]
  
  - from: "Internal"
    to: ["Confidential", "Secret"]
  
  - from: "Confidential"
    to: ["Secret"]
```

#### Declassification Rules
```yaml
# Emergency access declassification
declassify:
  rule: "emergency_access"
  source: "Secret"
  target: "Internal"
  condition: |
    attr(role) == "emergency_responder" AND
    incident.active == true AND
    approval.granted == true
```

### Field-Level IFC

#### Path-Based Access
```yaml
# Document structure with labels
document:
  id: "doc://project/requirements"
  label: "Confidential"
  fields:
    - path: ["metadata", "title"]
      label: "Internal"
    - path: ["data", "requirements"]
      label: "Confidential"
    - path: ["data", "budget"]
      label: "Secret"
```

#### Witness Validation
```yaml
# Field access requires valid witness
access:
  type: "read"
  field: ["data", "requirements"]
  requirements:
    - "valid_merkle_path"
    - "label_derivation_ok"
    - "epoch_validation"
```

## Unified Actions

### Action Types

#### Tool Calls
```yaml
# Email sending
action:
  type: "call"
  tool: "SendEmail"
  parameters:
    recipient: "user@example.com"
    subject: "Project Update"
    body: "Status report attached"
  access_control:
    role: "email_user"
    rate_limit: "10/hour"
    cost_limit: "$5.00"
```

#### Document Operations
```yaml
# Field read access
action:
  type: "read"
  resource:
    doc_id: "doc://team/project"
    path: ["data", "requirements"]
  access_control:
    role: "reader"
    project_match: true
    label_flow: true
```

#### Permission Grants
```yaml
# Delegating access
action:
  type: "grant"
  target: "user456"
  permission: "read"
  resource: "doc://team/project"
  scope: "data.requirements"
  ttl: "24h"
```

### Context Integration

#### Epoch Management
```yaml
# Epoch-based access control
context:
  epoch: 5
  current_epoch: 5
  epoch_validation: true
  
# Revocation support
revocation:
  epoch: 6
  reason: "Security incident"
  affected_principals: ["user123"]
  ttl: "2h"
```

#### Session Management
```yaml
# Session context
session:
  id: "sess_789"
  user: "user123"
  start_time: 1640995200
  attributes:
    location: "us-west"
    device: "mobile"
    risk_level: "low"
```

## Policy Enforcement

### Enforcement Modes

#### Shadow Mode
- **Purpose**: Policy validation without blocking
- **Use Case**: Initial deployment, testing
- **Behavior**: Logs decisions, allows all actions
- **Monitoring**: Tracks policy violations

#### Monitor Mode
- **Purpose**: Policy monitoring with violation tracking
- **Use Case**: Gradual rollout, compliance monitoring
- **Behavior**: Logs decisions, allows actions, tracks violations
- **Monitoring**: Comprehensive violation analysis

#### Enforce Mode
- **Purpose**: Full policy enforcement
- **Use Case**: Production deployment
- **Behavior**: Blocks denied actions, logs all decisions
- **Monitoring**: Real-time enforcement metrics

### Decision Pipeline

```
Event → Context Mapping → Policy Evaluation → Decision → Enforcement
  │           │              │              │          │
  ▼           ▼              ▼              ▼          ▼
Sidecar   Principal      permitD        Allow/    Block/Log
Event     Context       Function       Deny      Monitor
```

### Performance Optimization

#### Caching
```yaml
# Policy decision caching
cache:
  enabled: true
  ttl: "5m"
  max_size: 10000
  eviction: "lru"
  
# Context caching
context_cache:
  enabled: true
  ttl: "1m"
  max_size: 1000
```

#### Batch Processing
```yaml
# Batch policy evaluation
batch:
  enabled: true
  max_batch_size: 100
  timeout: "100ms"
  parallel_workers: 4
```

## Monitoring and Alerting

### Key Metrics

#### Policy Enforcement
- **Decision Rate**: Requests per second
- **Allow Rate**: Percentage of allowed requests
- **Deny Rate**: Percentage of denied requests
- **Latency**: P95 decision time

#### Security Metrics
- **Violation Rate**: Policy violations per minute
- **Witness Failures**: Invalid witness attempts
- **Epoch Violations**: Expired epoch access attempts
- **Label Flow Violations**: IFC policy violations

#### System Health
- **Certificate Verification**: Success rate
- **Replay Determinism**: Deterministic replay percentage
- **Resource Usage**: CPU, memory, network utilization

### Alert Rules

#### Critical Alerts
```yaml
# Policy enforcement failure
alert: PolicyEnforcementFailure
expr: up{job="sidecar-watcher"} == 0
for: 1m
severity: critical

# High violation rate
alert: HighViolationRate
expr: rate(policy_violations_total[5m]) > 0.1
for: 2m
severity: critical
```

#### Warning Alerts
```yaml
# Performance degradation
alert: PerformanceDegraded
expr: histogram_quantile(0.95, rate(decision_duration_seconds_bucket[5m])) > 0.1
for: 5m
severity: warning

# Certificate verification issues
alert: CertificateVerificationLow
expr: rate(certs_verified_total[5m]) / rate(certs_total[5m]) * 100 < 99.9
for: 2m
severity: warning
```

### Dashboards

#### Policy Enforcement Dashboard
- Real-time decision metrics
- Violation trends and patterns
- Performance indicators
- System health status

#### Security Dashboard
- Policy violation analysis
- IFC compliance metrics
- Witness validation status
- Revocation tracking

## Operational Procedures

### Deployment

#### Staging Deployment
```bash
# Deploy to staging
kubectl apply -f k8s/staging/

# Verify deployment
kubectl get pods -n staging
kubectl rollout status deployment/sidecar-watcher -n staging

# Run validation tests
./pfctl test --env staging --suite basic
```

#### Production Deployment
```bash
# Create backup
kubectl get deployment sidecar-watcher -n production -o yaml > backup.yaml

# Deploy with rolling update
kubectl set image deployment/sidecar-watcher -n production \
  sidecar-watcher=registry/provability-fabric/sidecar-watcher:v1.2.0

# Monitor rollout
kubectl rollout status deployment/sidecar-watcher -n production --timeout=600s
```

### Policy Updates

#### Configuration Changes
```bash
# Update policy configuration
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"enforcement_mode":"enforce"}}'

# Restart sidecar
kubectl rollout restart deployment/sidecar-watcher -n production

# Verify changes
./pfctl config show --env production
```

#### Emergency Changes
```bash
# Enable break-glass mode
./pfctl break-glass enable \
  --reason "Emergency policy update" \
  --duration "1h"

# Make emergency changes
./pfctl policy update --env production --file emergency-policy.yaml

# Disable break-glass mode
./pfctl break-glass disable
```

### Incident Response

#### Policy Violation
```bash
# Investigate violation
./pfctl analyze --violations violations.log --output analysis.json

# Check policy configuration
./pfctl config show --env production --format json > config.json

# Update policy if needed
./pfctl policy update --env production --file updated-policy.yaml
```

#### Performance Issues
```bash
# Check resource usage
kubectl top pods -n production

# Analyze metrics
kubectl port-forward -n production svc/prometheus 9090:9090

# Scale resources if needed
kubectl scale deployment sidecar-watcher -n production --replicas=3
```

## Troubleshooting

### Common Issues

#### Policy Adapter Not Responding
```bash
# Check pod status
kubectl get pods -n production -l app=policy-adapter

# Check logs
kubectl logs -n production -l app=policy-adapter --tail=100

# Check health endpoint
kubectl exec -n production deployment/policy-adapter -- \
  curl -f http://localhost:8080/health
```

#### High Reject Rates
```bash
# Analyze reject patterns
kubectl logs -n production -l app=sidecar-watcher | \
  grep "REJECT" | jq .

# Check policy configuration
./pfctl config show --env production

# Verify DFA integrity
sha256sum artifact/dfa.json
```

#### Performance Issues
```bash
# Check resource constraints
kubectl describe nodes | grep -A 10 "Allocated resources"

# Analyze performance metrics
kubectl port-forward -n production svc/prometheus 9090:9090

# Check for bottlenecks
kubectl logs -n production -l app=sidecar-watcher | \
  grep -E "(SLOW|TIMEOUT|ERROR)"
```

### Debug Mode

#### Enable Debug Logging
```bash
# Enable debug mode
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"log_level":"debug"}}'

# Restart sidecar
kubectl rollout restart deployment/sidecar-watcher -n production

# Collect debug logs
kubectl logs -n production -l app=sidecar-watcher --tail=1000 > debug.log
```

#### Performance Profiling
```bash
# Enable profiling
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"profiling_enabled":"true"}}'

# Access profiling data
kubectl port-forward -n production svc/sidecar-watcher 6060:6060
# Open http://localhost:6060/debug/pprof/
```

### Recovery Procedures

#### Policy Rollback
```bash
# Rollback to previous version
kubectl rollout undo deployment/sidecar-watcher -n production

# Verify rollback
kubectl rollout status deployment/sidecar-watcher -n production
kubectl get pods -n production
```

#### Configuration Recovery
```bash
# Restore configuration
kubectl apply -f backup.yaml

# Restart sidecar
kubectl rollout restart deployment/sidecar-watcher -n production

# Verify restoration
./pfctl config show --env production
```

## Best Practices

### Policy Design

1. **Principle of Least Privilege**: Grant minimum necessary permissions
2. **Defense in Depth**: Multiple layers of access control
3. **Fail-Safe Defaults**: Deny by default, allow by exception
4. **Regular Review**: Periodic policy review and updates
5. **Testing**: Comprehensive testing of policy changes

### Operational Excellence

1. **Monitoring**: Comprehensive monitoring and alerting
2. **Documentation**: Clear documentation of policies and procedures
3. **Training**: Regular team training on policy management
4. **Incident Response**: Well-defined incident response procedures
5. **Continuous Improvement**: Regular process improvement cycles

### Security Considerations

1. **Audit Logging**: Comprehensive audit trail of all decisions
2. **Cryptographic Verification**: Cryptographic validation of access paths
3. **Time-Bounded Access**: Automatic expiration of permissions
4. **Revocation Support**: Quick revocation of compromised access
5. **Compliance**: Regular compliance audits and reporting

## Conclusion

The Provability Fabric policy enforcement system provides a robust, secure, and auditable foundation for access control. By combining ABAC, IFC, and unified actions with formal verification and runtime enforcement, the system ensures that security policies are correctly implemented and enforced.

For additional information, see:
- [Policy DSL Documentation](dsl.md)
- [Certificate Schema](certs.md)
- [Epoch Management](epochs.md)
- [Operational Runbooks](../runbooks/)
