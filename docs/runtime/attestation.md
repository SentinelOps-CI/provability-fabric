# Runtime Attestation Verification

This document describes how to verify runtime attestation locally for the Provability-Fabric system.

## Overview

Runtime attestation ensures that only attested runtimes can access sensitive operations like KMS operations. The attestation process includes:

1. **Policy Hash Verification**: Ensures the runtime is running with the expected policy
2. **Pod Identity Binding**: Links attestation to specific pod identity
3. **Zero-Retention Flag**: Indicates whether the runtime implements zero-retention policies
4. **Time-Based Validation**: Attestation tokens expire after 60 seconds

## Attestation Structure

```json
{
  "token": "attestation_token_string",
  "pod_identity": "pod-secure-1",
  "policy_hash": "default_policy_hash",
  "timestamp": "2025-01-27T10:30:00Z",
  "signature": "sig_1234567890"
}
```

## Local Verification Process

### 1. Extract Attestation from Runtime

```bash
# Get attestation from running pod
kubectl exec -it <pod-name> -- cat /var/run/attestation.json
```

### 2. Verify Policy Hash

```python
import hashlib
import json

def verify_policy_hash(attestation_data, expected_policy):
    """Verify that the policy hash matches expected policy"""
    policy_hash = hashlib.sha256(expected_policy.encode()).hexdigest()
    return attestation_data['policy_hash'] == policy_hash

# Example usage
with open('attestation.json', 'r') as f:
    attestation = json.load(f)

expected_policy = """
# Your expected policy content
"""
is_valid = verify_policy_hash(attestation, expected_policy)
print(f"Policy hash valid: {is_valid}")
```

### 3. Verify Pod Identity

```python
def verify_pod_identity(attestation_data, allowed_identities):
    """Verify that pod identity is in allowed list"""
    pod_id = attestation_data['pod_identity']
    return pod_id in allowed_identities

# Example usage
allowed_pods = ['pod-secure-1', 'pod-secure-2']
is_allowed = verify_pod_identity(attestation, allowed_pods)
print(f"Pod identity allowed: {is_allowed}")
```

### 4. Check Token Freshness

```python
from datetime import datetime, timezone
import pytz

def verify_token_freshness(attestation_data, max_age_seconds=60):
    """Verify that attestation token is fresh"""
    timestamp_str = attestation_data['timestamp']
    token_time = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
    now = datetime.now(timezone.utc)
    
    age_seconds = (now - token_time).total_seconds()
    return age_seconds <= max_age_seconds

# Example usage
is_fresh = verify_token_freshness(attestation)
print(f"Token is fresh: {is_fresh}")
```

### 5. Verify Signature

```python
import hmac
import hashlib

def verify_signature(attestation_data, secret_key):
    """Verify the cryptographic signature"""
    # Create the content that was signed
    content = (
        f"{attestation_data['timestamp']}"
        f"{attestation_data['pod_identity']}"
        f"{attestation_data['policy_hash']}"
    )
    
    # Create expected signature
    expected_sig = hmac.new(
        secret_key.encode(),
        content.encode(),
        hashlib.sha256
    ).hexdigest()
    
    return attestation_data['signature'] == expected_sig

# Example usage
secret_key = "your-secret-key"
is_signed = verify_signature(attestation, secret_key)
print(f"Signature valid: {is_signed}")
```

## Complete Verification Script

```python
#!/usr/bin/env python3
"""
Complete attestation verification script
"""

import json
import hashlib
import hmac
from datetime import datetime, timezone
from typing import Dict, Any

class AttestationVerifier:
    def __init__(self, allowed_pods: list, allowed_policies: list, secret_key: str):
        self.allowed_pods = allowed_pods
        self.allowed_policies = allowed_policies
        self.secret_key = secret_key
        
    def verify_attestation(self, attestation_data: Dict[str, Any]) -> Dict[str, Any]:
        """Complete attestation verification"""
        results = {
            'valid': True,
            'errors': [],
            'warnings': []
        }
        
        # Check policy hash
        if attestation_data['policy_hash'] not in self.allowed_policies:
            results['valid'] = False
            results['errors'].append(f"Policy hash {attestation_data['policy_hash']} not allowed")
            
        # Check pod identity
        if attestation_data['pod_identity'] not in self.allowed_pods:
            results['valid'] = False
            results['errors'].append(f"Pod identity {attestation_data['pod_identity']} not allowed")
            
        # Check token freshness
        if not self._verify_freshness(attestation_data):
            results['valid'] = False
            results['errors'].append("Attestation token expired")
            
        # Check signature
        if not self._verify_signature(attestation_data):
            results['valid'] = False
            results['errors'].append("Invalid signature")
            
        return results
        
    def _verify_freshness(self, attestation_data: Dict[str, Any], max_age_seconds: int = 60) -> bool:
        """Verify token is fresh"""
        timestamp_str = attestation_data['timestamp']
        token_time = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
        now = datetime.now(timezone.utc)
        
        age_seconds = (now - token_time).total_seconds()
        return age_seconds <= max_age_seconds
        
    def _verify_signature(self, attestation_data: Dict[str, Any]) -> bool:
        """Verify cryptographic signature"""
        content = (
            f"{attestation_data['timestamp']}"
            f"{attestation_data['pod_identity']}"
            f"{attestation_data['policy_hash']}"
        )
        
        expected_sig = hmac.new(
            self.secret_key.encode(),
            content.encode(),
            hashlib.sha256
        ).hexdigest()
        
        return attestation_data['signature'] == expected_sig

def main():
    # Configuration
    allowed_pods = ['pod-secure-1', 'pod-secure-2']
    allowed_policies = ['default_policy_hash', 'secure_policy_hash']
    secret_key = "your-secret-key-here"
    
    verifier = AttestationVerifier(allowed_pods, allowed_policies, secret_key)
    
    # Load attestation data
    with open('attestation.json', 'r') as f:
        attestation = json.load(f)
    
    # Verify attestation
    result = verifier.verify_attestation(attestation)
    
    if result['valid']:
        print("✓ Attestation verification passed")
    else:
        print("✗ Attestation verification failed:")
        for error in result['errors']:
            print(f"  - {error}")
            
    return result['valid']

if __name__ == "__main__":
    main()
```

## Integration with KMS Proxy

The KMS proxy automatically verifies attestation tokens before allowing any cryptographic operations:

```bash
# Example KMS request with attestation
curl -X POST http://localhost:8082/kms/encrypt \
  -H "Content-Type: application/json" \
  -d '{
    "operation": "encrypt",
    "key_id": "key-123",
    "data": "sensitive-data",
    "attestation_token": {
      "token": "attestation_token_string",
      "pod_identity": "pod-secure-1",
      "policy_hash": "default_policy_hash",
      "timestamp": "2025-01-27T10:30:00Z",
      "signature": "sig_1234567890"
    }
  }'
```

## Security Considerations

1. **Key Rotation**: Attestation keys should be rotated regularly
2. **Token Expiration**: Tokens expire after 60 seconds to limit exposure
3. **Policy Validation**: Only approved policy hashes are accepted
4. **Pod Identity**: Only known pod identities are allowed
5. **Signature Verification**: All attestations must be cryptographically signed

## Troubleshooting

### Common Issues

1. **Token Expired**: Check system time synchronization
2. **Invalid Policy Hash**: Verify policy configuration
3. **Unknown Pod Identity**: Add pod to allowed list
4. **Invalid Signature**: Check key configuration

### Debug Commands

```bash
# Check attestation in pod
kubectl exec -it <pod-name> -- cat /var/run/attestation.json

# Verify attestation locally
python3 verify_attestation.py

# Test KMS proxy
curl -X POST http://localhost:8082/kms/encrypt -H "Content-Type: application/json" -d '{"operation":"encrypt","key_id":"test","data":"test"}'
```