# Safety Case Documentation

## Overview

Safety Cases provide formal evidence that the Provability Fabric system maintains security properties across all sessions. Each session generates a complete bundle of artifacts that demonstrate compliance with security requirements.

## Session Safety Case Structure

### Required Artifacts Per Session

```json
{
  "session_id": "session_20241201_001",
  "tenant": "acme_corp",
  "timestamp": "2024-12-01T10:00:00Z",
  "artifacts": {
    "plans": [
      {
        "plan_id": "plan_20241201_001",
        "hash": "sha256:abc123...",
        "validated": true,
        "kernel_checks": {
          "capability_match": "PASS",
          "receipt_presence": "PASS",
          "label_flow": "PASS"
        }
      }
    ],
    "receipts": [
      {
        "receipt_id": "receipt_20241201_001",
        "type": "access_receipt",
        "partition": "tenant:acme",
        "hash": "sha256:def456...",
        "expires": "2024-12-01T11:00:00Z",
        "valid": true
      }
    ],
    "certificates": [
      {
        "certificate_id": "cert_20241201_001",
        "non_interference": "passed",
        "hash": "sha256:ghi789...",
        "evidence_chain": ["receipt_20241201_001"]
      }
    ],
    "evidence": [
      {
        "evidence_id": "evidence_20241201_001",
        "type": "kernel_decision",
        "timestamp": "2024-12-01T09:55:00Z",
        "hash": "sha256:jkl012...",
        "decision": "ALLOW",
        "reason": "ALL_CHECKS_PASSED"
      }
    ],
    "proofs": [
      {
        "proof_id": "proof_20241201_001",
        "type": "lean_proof",
        "theorem": "thm_plan_sound",
        "hash": "sha256:mno345...",
        "verified": true
      }
    ]
  },
  "compliance_summary": {
    "total_plans": 1,
    "valid_plans": 1,
    "total_receipts": 1,
    "valid_receipts": 1,
    "total_certificates": 1,
    "ni_passed": 1,
    "ni_failed": 0,
    "total_evidence": 1,
    "total_proofs": 1,
    "verified_proofs": 1
  }
}
```

## Artifact Types

### 1. Plans
- **Purpose**: Execution plans validated by Policy Kernel
- **Required Fields**: plan_id, hash, validated, kernel_checks
- **Validation**: Must pass all three kernel checks
- **Storage**: Indexed by session and tenant

### 2. Receipts
- **Purpose**: Access receipts for data retrieval
- **Required Fields**: receipt_id, type, partition, hash, expires, valid
- **Validation**: Must be unexpired and cover correct partition
- **Types**: access_receipt, policy_receipt, capability_receipt

### 3. Certificates
- **Purpose**: Egress certificates with NI verdicts
- **Required Fields**: certificate_id, non_interference, hash, evidence_chain
- **Validation**: Must have valid NI verdict and evidence chain
- **NI Values**: passed, failed, unknown

### 4. Evidence
- **Purpose**: Decision logs and audit trail
- **Required Fields**: evidence_id, type, timestamp, hash, decision, reason
- **Types**: kernel_decision, receipt_validation, ni_check, budget_check
- **Validation**: Must be cryptographically signed

### 5. Proofs
- **Purpose**: Formal Lean proofs of security properties
- **Required Fields**: proof_id, type, theorem, hash, verified
- **Types**: lean_proof, formal_verification, attestation
- **Validation**: Must be verified by Lean theorem prover

## Compliance Requirements

### Session-Level Requirements
1. **Complete Artifact Chain**: Every session must have at least one plan, receipt, certificate, evidence, and proof
2. **Valid Artifacts**: All artifacts must be valid (validated=true, verified=true)
3. **NI Compliance**: All certificates must have non_interference="passed"
4. **Receipt Coverage**: Every data access must have corresponding receipt
5. **Evidence Integrity**: All evidence must be cryptographically signed

### Tenant-Level Requirements
1. **Session Isolation**: No cross-tenant artifact sharing
2. **Receipt Partitioning**: Receipts must match tenant partitions
3. **Capability Boundaries**: Plans must respect tenant capability limits
4. **Evidence Chain**: Complete audit trail per tenant

### System-Level Requirements
1. **Non-Interference**: 100% of certificates must have NI="passed"
2. **Proof Verification**: 100% of proofs must be verified
3. **Receipt Validation**: 100% of receipts must be valid
4. **Plan Validation**: 100% of plans must pass kernel checks

## Safety Case Generation

### Automatic Generation
Safety cases are automatically generated for each session:

```python
def generate_safety_case(session_id: str) -> SafetyCase:
    # Collect all artifacts for session
    plans = get_session_plans(session_id)
    receipts = get_session_receipts(session_id)
    certificates = get_session_certificates(session_id)
    evidence = get_session_evidence(session_id)
    proofs = get_session_proofs(session_id)
    
    # Validate compliance
    compliance = validate_compliance(plans, receipts, certificates, evidence, proofs)
    
    # Generate safety case
    return SafetyCase(
        session_id=session_id,
        artifacts={
            "plans": plans,
            "receipts": receipts,
            "certificates": certificates,
            "evidence": evidence,
            "proofs": proofs
        },
        compliance_summary=compliance
    )
```

### Manual Review
Safety cases can be manually reviewed for compliance:

```bash
# Review safety case for session
python tools/compliance/review_safety_case.py session_20241201_001

# Validate all safety cases for tenant
python tools/compliance/validate_tenant_safety.py acme_corp

# Generate compliance report
python tools/compliance/generate_report.py --tenant acme_corp --date 2024-12-01
```

## Compliance Monitoring

### Real-Time Monitoring
- **Session Completion**: Track artifact completeness per session
- **NI Compliance**: Monitor non-interference verdicts
- **Proof Verification**: Track Lean proof verification status
- **Receipt Validation**: Monitor receipt validity and expiration

### Periodic Audits
- **Daily**: Generate compliance summary for all sessions
- **Weekly**: Review safety cases for policy violations
- **Monthly**: Comprehensive compliance audit report

### Alerting
- **Missing Artifacts**: Alert when session lacks required artifacts
- **NI Failures**: Alert on non-interference violations
- **Proof Failures**: Alert when proofs fail verification
- **Receipt Expiration**: Alert on expired receipts

## Integration with CI/CD

### Safety Case Validation
```yaml
# .github/workflows/safety-case-validation.yaml
name: Safety Case Validation
on: [push, pull_request]
jobs:
  validate-safety-cases:
    runs-on: ubuntu-latest
    steps:
      - name: Validate Session Safety Cases
        run: |
          python tools/compliance/validate_safety_cases.py
          # Ensures 100% artifact completeness
          # Validates NI compliance
          # Verifies proof integrity
```

### Compliance Gates
- **Session Completeness**: 100% of sessions have complete artifact sets
- **NI Compliance**: 100% of certificates have NI="passed"
- **Proof Verification**: 100% of proofs are verified
- **Receipt Validation**: 100% of receipts are valid

## Security Properties

### Confidentiality
- **Tenant Isolation**: No cross-tenant data leakage
- **Receipt Partitioning**: Data access limited to authorized partitions
- **NI Enforcement**: Untrusted inputs cannot influence trusted outputs

### Integrity
- **Cryptographic Signatures**: All artifacts cryptographically signed
- **Hash Verification**: Content integrity verified via hashes
- **Evidence Chain**: Complete audit trail for all decisions

### Availability
- **Session Persistence**: All artifacts persisted for audit
- **Real-Time Generation**: Safety cases generated immediately
- **High Throughput**: Designed for production load

## Compliance Reporting

### Session Reports
```json
{
  "session_id": "session_20241201_001",
  "compliance_status": "COMPLIANT",
  "artifacts_complete": true,
  "ni_compliant": true,
  "proofs_verified": true,
  "receipts_valid": true,
  "violations": []
}
```

### Tenant Reports
```json
{
  "tenant": "acme_corp",
  "date": "2024-12-01",
  "total_sessions": 150,
  "compliant_sessions": 150,
  "ni_passed": 150,
  "ni_failed": 0,
  "compliance_rate": 1.0
}
```

### System Reports
```json
{
  "date": "2024-12-01",
  "total_sessions": 1500,
  "compliant_sessions": 1500,
  "ni_passed": 1500,
  "ni_failed": 0,
  "proofs_verified": 1500,
  "receipts_valid": 1500,
  "overall_compliance": 1.0
}
```

## Links

- [Safety Case Validation](/tools/compliance/validate_safety_cases.py)
- [Compliance Monitoring](/tools/compliance/monitor_compliance.py)
- [Lean Proofs](/core/lean-libs/)
- [Policy Kernel](/core/policy-kernel/engine.go)
- [Egress Certificates](/docs/spec/egress-certificate.md) 