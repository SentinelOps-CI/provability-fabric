# Egress Certificate Specification

## Overview

Egress Certificates provide cryptographic proof that system outputs comply with security policies and data handling requirements. Each certificate contains 8 required fields including a Non-Interference (NI) verdict.

## Certificate Structure

```json
{
  "certificate_id": "cert_20241201_001",
  "session_id": "session_20241201_001",
  "timestamp": "2024-12-01T10:00:00Z",
  "non_interference": "passed",
  "evidence_chain": [
    {
      "receipt_id": "receipt_20241201_001",
      "hash": "sha256:abc123...",
      "timestamp": "2024-12-01T09:55:00Z"
    }
  ],
  "policy_compliance": {
    "capability_check": "PASS",
    "receipt_validation": "PASS", 
    "label_flow": "PASS",
    "budget_enforcement": "PASS"
  },
  "signature": {
    "algorithm": "RS256",
    "key_id": "key_20241201_001",
    "signature": "base64_encoded_signature..."
  },
  "metadata": {
    "tenant": "acme_corp",
    "subject": "user_123",
    "plan_id": "plan_20241201_001",
    "output_labels": ["tenant:acme", "pii:masked"]
  }
}
```

## Required Fields

### 1. certificate_id
- **Type**: String
- **Format**: `cert_YYYYMMDD_XXX`
- **Purpose**: Unique identifier for the certificate
- **Validation**: Must be unique within the system

### 2. session_id  
- **Type**: String
- **Format**: `session_YYYYMMDD_XXX`
- **Purpose**: Links certificate to specific session
- **Validation**: Must reference valid session

### 3. timestamp
- **Type**: ISO 8601 DateTime
- **Format**: `YYYY-MM-DDTHH:MM:SSZ`
- **Purpose**: Certificate generation time
- **Validation**: Must be current time ±5 minutes

### 4. non_interference
- **Type**: String
- **Values**: `"passed"`, `"failed"`, `"unknown"`
- **Purpose**: NI verdict indicating if untrusted inputs affected trusted outputs
- **Validation**: Must be one of the three allowed values

### 5. evidence_chain
- **Type**: Array of Evidence Objects
- **Purpose**: Links to all receipts and evidence used in decision
- **Validation**: Must contain at least one valid receipt

### 6. policy_compliance
- **Type**: Object with check results
- **Purpose**: Detailed results of all kernel checks
- **Validation**: All checks must have PASS/FAIL values

### 7. signature
- **Type**: Cryptographic signature object
- **Purpose**: Cryptographic proof of certificate authenticity
- **Validation**: Must be valid signature from authorized key

### 8. metadata
- **Type**: Object with session metadata
- **Purpose**: Additional context for certificate validation
- **Validation**: Must contain required tenant and subject fields

## Non-Interference Verdict

The `non_interference` field is critical for security compliance:

### "passed"
- Untrusted inputs did not influence trusted outputs
- System behavior remained consistent with policy
- All data flows respected security boundaries

### "failed"  
- Untrusted inputs affected trusted outputs
- Potential security violation detected
- Certificate should trigger security alert

### "unknown"
- Unable to determine NI status
- Requires manual review
- May indicate system configuration issues

## Evidence Chain Format

```json
{
  "evidence_chain": [
    {
      "receipt_id": "receipt_20241201_001",
      "hash": "sha256:abc123...",
      "timestamp": "2024-12-01T09:55:00Z",
      "type": "access_receipt",
      "partition": "tenant:acme",
      "expires": "2024-12-01T11:00:00Z"
    },
    {
      "receipt_id": "receipt_20241201_002", 
      "hash": "sha256:def456...",
      "timestamp": "2024-12-01T09:56:00Z",
      "type": "policy_receipt",
      "policy_hash": "sha256:ghi789...",
      "expires": "2024-12-01T11:00:00Z"
    }
  ]
}
```

## Policy Compliance Checks

```json
{
  "policy_compliance": {
    "capability_check": "PASS",
    "receipt_validation": "PASS",
    "label_flow": "PASS", 
    "budget_enforcement": "PASS",
    "injection_prevention": "PASS",
    "data_retention": "PASS",
    "privacy_compliance": "PASS"
  }
}
```

## Signature Verification

Certificates are signed using RS256 with the following structure:

```json
{
  "signature": {
    "algorithm": "RS256",
    "key_id": "key_20241201_001",
    "signature": "base64_encoded_signature...",
    "certificate_chain": [
      "base64_encoded_cert1...",
      "base64_encoded_cert2..."
    ]
  }
}
```

## Validation Rules

1. **Certificate ID**: Must be unique and follow naming convention
2. **Session Link**: Must reference valid, unexpired session
3. **Timestamp**: Must be within acceptable time window
4. **NI Verdict**: Must be one of three allowed values
5. **Evidence**: Must contain at least one valid receipt
6. **Compliance**: All policy checks must have valid results
7. **Signature**: Must be cryptographically valid
8. **Metadata**: Must contain required tenant and subject information

## Error Handling

Invalid certificates return structured errors:

```json
{
  "error": "INVALID_CERTIFICATE",
  "reason": "MISSING_NI_VERDICT",
  "certificate_id": "cert_20241201_001",
  "timestamp": "2024-12-01T10:00:00Z"
}
```

## Integration with CI/CD

Certificates are validated in CI jobs:

- **certificate-validation**: Verifies all 8 fields present
- **ni-verdict-check**: Ensures NI verdict is valid
- **signature-verification**: Validates cryptographic signatures
- **evidence-chain-validation**: Confirms evidence integrity

## Security Properties

- **Non-repudiation**: Cryptographic signatures prevent tampering
- **Audit Trail**: Complete evidence chain for compliance
- **NI Enforcement**: Prevents untrusted influence on trusted outputs
- **Policy Compliance**: All security checks documented
- **Session Isolation**: Certificates bound to specific sessions 