# Attestation Verification Guide

## Overview

This document provides instructions for verifying enclave attestations in Provability Fabric. The system supports both AWS Nitro and AMD SEV attestation mechanisms.

## AWS Nitro Attestation

### Verification Commands

```bash
# Verify Nitro attestation document
curl -X POST http://localhost:8080/verify/nitro \
  -H "Content-Type: application/json" \
  -d @nitro_attestation.json

# Check expected measurements
curl http://localhost:8080/measurements/nitro
```

### Expected Measurements

```json
{
  "expected_pcrs": {
    "0": "0000000000000000000000000000000000000000000000000000000000000000",
    "1": "1111111111111111111111111111111111111111111111111111111111111111",
    "2": "2222222222222222222222222222222222222222222222222222222222222222"
  },
  "expected_module_id": "test-module-123",
  "expected_digest": "test-digest-456",
  "max_age_seconds": 3600
}
```

## AMD SEV Attestation

### Verification Commands

```bash
# Verify SEV attestation report
curl -X POST http://localhost:8080/verify/sev \
  -H "Content-Type: application/json" \
  -d @sev_report.json

# Check expected measurements
curl http://localhost:8080/measurements/sev
```

### Expected Measurements

```json
{
  "expected_measurement": "123456000000000000000000000000000000000000000000",
  "expected_family_id": "aabb000000000000000000000000000000",
  "expected_image_id": "ccdd000000000000000000000000000000",
  "expected_policy": {
    "debug": false,
    "migratable": false,
    "smt": false,
    "reserved": 0
  },
  "min_tcb_version": {
    "major": 0,
    "minor": 0,
    "build": 0,
    "build_id": 0
  },
  "max_age_seconds": 3600
}
```

## KMS Token Generation

### Generate Attested Token

```bash
# Generate KMS token with attestation
curl -X POST http://localhost:8080/token/generate \
  -H "Content-Type: application/json" \
  -d '{
    "attestation_data": "base64_encoded_attestation",
    "kms_config": {
      "region": "us-west-2",
      "key_id": "alias/provability-fabric",
      "token_ttl": 3600,
      "require_attestation": true
    }
  }'
```

### Verify Token

```bash
# Verify KMS token
curl -X POST http://localhost:8080/token/verify \
  -H "Content-Type: application/json" \
  -d '{"token": "base64_encoded_token"}'
```

## Testing

### Unit Tests

```bash
# Run Nitro attestation tests
cargo test --package attestor --test nitro

# Run SEV attestation tests  
cargo test --package attestor --test sev

# Run KMS integration tests
cargo test --package attestor --test kms
```

### Integration Tests

```bash
# Test with tampered attestation (should DENY)
curl -X POST http://localhost:8080/verify/nitro \
  -H "Content-Type: application/json" \
  -d @tampered_nitro.json

# Test without attestation (should DENY)
curl -X POST http://localhost:8080/token/generate \
  -H "Content-Type: application/json" \
  -d '{"kms_config": {"require_attestation": true}}'
```

## Configuration

### Environment Variables

```bash
# Attestation settings
ATTESTATION_REQUIRED=true
NITRO_MEASUREMENTS_FILE=/etc/provability-fabric/nitro-measurements.json
SEV_MEASUREMENTS_FILE=/etc/provability-fabric/sev-measurements.json

# KMS settings
KMS_REGION=us-west-2
KMS_KEY_ID=alias/provability-fabric
KMS_TOKEN_TTL=3600
KMS_REQUIRE_ATTESTATION=true
```

### Measurement Rotation

To rotate measurements:

1. Update the measurements files
2. Restart the attestor service
3. Verify CI tests pass with new measurements
4. Deploy to production

**Note**: Measurement rotation will cause CI failures if not properly configured, ensuring security.

## Security Considerations

- Attestation quotes are cryptographically verified
- Measurements are bound to expected values
- Short-lived tokens prevent long-term access
- Policy violations are logged and monitored
- Debug mode is disabled in production

