# Runtime Attestation

## Overview

The Attestor service provides continuous attestation of runtime configuration and security mechanisms. It emits signed attestations at regular intervals to prove the system is operating within defined security parameters.

## Architecture

```
Attestor → Generate Attestation → Sign with DSSE → Submit to Ledger
```

## Attestation Contents

Each attestation includes:

### Core Fields
- `attestation_id`: Unique identifier for the attestation
- `timestamp`: Unix timestamp of attestation generation
- `policy_hash`: Hash of active policy configuration
- `zero_retention`: Flag indicating data retention policy

### Privacy Limits
- `epsilon_limits`: Current differential privacy configuration
  - `max_epsilon`: Maximum epsilon allowed
  - `max_delta`: Maximum delta allowed  
  - `current_usage`: Current epsilon consumption
  - `reset_interval`: Budget reset interval

### System Configuration
- `version`: Software version
- `kernel_config_hash`: Hash of policy kernel configuration
- `capability_keys`: Active capability signing keys
- `tenant_isolation`: Tenant isolation status
- `egress_firewall_enabled`: Egress firewall status
- `pii_detection_enabled`: PII detection status

### Runtime Metrics
- `total_requests`: Total requests processed
- `blocked_requests`: Requests blocked by policies
- `capability_failures`: Capability validation failures
- `plan_validations`: Plan validation attempts
- `uptime_seconds`: System uptime

## Heartbeat Schedule

- **Interval**: 60 seconds (configurable)
- **Timeout**: 15 seconds maximum
- **Failure Handling**: Missing heartbeats trigger alerts

## Validation

Attestations are validated for:
1. **Freshness**: Timestamp within 5 minutes
2. **Policy Consistency**: Policy hash matches expected
3. **Configuration Drift**: Zero retention flag unchanged
4. **Signature Integrity**: DSSE signature verification

## Security Properties

- **Tamper Evidence**: Configuration changes are immediately visible
- **Non-Repudiation**: Signed attestations provide audit trail
- **Real-time Monitoring**: Continuous verification of security posture
- **Drift Detection**: Automated alerting on configuration changes

## Integration

### Ledger Storage
Attestations are stored in the ledger with:
- Immutable timestamp ordering
- Cryptographic integrity protection
- Query interface for audit trail

### Monitoring
- Prometheus metrics for attestation frequency
- Alerting on missing or invalid attestations
- Dashboard visualization of security posture

### CI/CD Integration
- Release gates check for healthy attestations
- Deployment blocked if attestation failures detected
- Automated rollback on attestation anomalies

## Usage

```rust
use attestor::{Attestor, AttestorConfig};

let config = AttestorConfig {
    attestation_interval: Duration::from_secs(60),
    policy_hash: "current_policy_hash".to_string(),
    zero_retention: true,
    ledger_endpoint: "https://ledger.example.com".to_string(),
    // ... other config
};

let mut attestor = Attestor::new(config);
attestor.start_heartbeat().await?;
```

## Failure Modes

### Missing Attestations
- **Cause**: Service failure or network issues
- **Detection**: Ledger monitors for gaps > 2 minutes
- **Response**: Automatic alerts, traffic throttling

### Invalid Attestations  
- **Cause**: Configuration drift or compromise
- **Detection**: Signature or content validation failure
- **Response**: Immediate security alert, traffic blocking

### Policy Drift
- **Cause**: Unauthorized configuration changes
- **Detection**: Policy hash mismatch in attestation
- **Response**: Automated rollback, incident response

## Compliance

Attestations provide evidence for:
- **SOC 2**: Continuous monitoring of security controls
- **ISO 27001**: Configuration management compliance
- **GDPR**: Data retention policy enforcement
- **FedRAMP**: Continuous monitoring requirements