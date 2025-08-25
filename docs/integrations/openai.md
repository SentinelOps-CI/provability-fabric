# OpenAI Integration Guide

## Overview

This guide shows how to integrate Provability Fabric with OpenAI's API to enforce security policies and maintain audit trails. The integration ensures proper channel classification, receipt management, and certificate generation.

## Quick Start

### 1. Install the SDK

```bash
pip install provability-fabric
```

### 2. Basic Integration

```python
from provability_fabric import ProvabilityFabric
from provability_fabric.types import Plan, Subject, AccessReceipt

# Initialize the client
pf = ProvabilityFabric(
    ledger_url="https://ledger.provability-fabric.com",
    policy_kernel_url="https://kernel.provability-fabric.com"
)

# Create a plan for OpenAI API call
plan = Plan(
    plan_id="openai_call_001",
    tenant="acme_corp",
    subject=Subject(
        id="user_123",
        caps=["openai_chat", "data_retrieval"]
    ),
    input_channels={
        "system": {
            "hash": "sha256:abc123...",
            "policy_hash": "sha256:def456..."
        },
        "user": {
            "content_hash": "sha256:ghi789...",
            "quoted": True
        },
        "retrieved": [
            {
                "receipt_id": "receipt_001",
                "content_hash": "sha256:jkl012...",
                "quoted": True,
                "labels": ["tenant:acme", "pii:masked"]
            }
        ]
    },
    steps=[
        {
            "tool": "openai_chat_completion",
            "args": {
                "model": "gpt-4",
                "messages": [
                    {"role": "system", "content": "You are a helpful assistant."},
                    {"role": "user", "content": "{{user_input}}"}
                ]
            },
            "caps_required": ["openai_chat"],
            "labels_in": ["tenant:acme", "pii:masked"],
            "labels_out": ["tenant:acme", "pii:masked"]
        }
    ],
    constraints={
        "budget": 1.0,
        "pii": False,
        "dp_epsilon": 0.1,
        "dp_delta": 1e-6,
        "latency_max": 30.0
    }
)

# Validate the plan
validation = pf.validate_plan(plan)
if not validation.valid:
    print(f"Plan validation failed: {validation.errors}")
    exit(1)

# Execute the plan
result = pf.execute_plan(plan)
print(f"Response: {result.response}")
print(f"Certificate: {result.certificate}")
```

## Channel Classification

### Trusted Channels (System/Policy)

```python
# System prompts and policy configuration
system_channel = {
    "hash": "sha256:abc123...",
    "policy_hash": "sha256:def456...",
    "immutable": True,
    "elevation_allowed": False
}

# Policy configuration
policy_config = {
    "max_tokens": 1000,
    "temperature": 0.7,
    "allowed_models": ["gpt-4", "gpt-3.5-turbo"],
    "forbidden_content": ["pii", "secrets", "malicious_code"]
}
```

### Untrusted Channels (User/Retrieved/File)

```python
# User input - must be quoted
user_input = {
    "content_hash": "sha256:ghi789...",
    "quoted": True,  # Required to prevent injection
    "elevation_allowed": False,
    "max_length": 10000
}

# Retrieved content - must have receipt
retrieved_content = {
    "receipt_id": "receipt_001",
    "content_hash": "sha256:jkl012...",
    "quoted": True,
    "labels": ["tenant:acme", "pii:masked"],
    "elevation_allowed": False
}

# File uploads - must be quoted
file_content = {
    "sha256": "sha256:mno345...",
    "media_type": "application/pdf",
    "quoted": True,
    "elevation_allowed": False,
    "max_size": 10485760
}
```

## Receipt Management

### Creating Access Receipts

```python
# Before retrieving data, create a receipt
receipt = pf.create_access_receipt(
    tenant="acme_corp",
    subject_id="user_123",
    query_hash="sha256:query_hash_here",
    index_shard="tenant:acme",
    partition="user_data"
)

# Use the receipt in your plan
plan.input_channels.retrieved.append({
    "receipt_id": receipt.receipt_id,
    "content_hash": receipt.result_hash,
    "quoted": True,
    "labels": ["tenant:acme", "pii:masked"]
})
```

### Validating Receipts

```python
# Validate receipt before use
is_valid = pf.validate_receipt(receipt.receipt_id)
if not is_valid:
    print("Receipt validation failed")
    exit(1)
```

## Certificate Handling

### Reading Egress Certificates

```python
# After API call, check the certificate
certificate = result.certificate

print(f"Certificate ID: {certificate.certificate_id}")
print(f"Non-Interference: {certificate.non_interference}")
print(f"Confidence: {certificate.confidence}")

# Check if NI passed
if certificate.non_interference == "passed":
    print("PASSED Non-interference check passed")
else:
    print("FAILED Non-interference violation detected")
    # Handle violation appropriately
```

### Displaying Confidence

```python
def display_confidence(certificate):
    if certificate.non_interference == "passed":
        badge_color = "green"
        icon = "PASSED"
    else:
        badge_color = "red"
        icon = "FAILED"
    
    print(f"{icon} NI {certificate.non_interference.upper()}")
    print(f"Confidence: {certificate.confidence:.1%}")
    print(f"Sources: {len(certificate.evidence_chain)} receipts")
```

## Error Handling

### Plan Validation Errors

```python
try:
    validation = pf.validate_plan(plan)
    if not validation.valid:
        for error in validation.errors:
            if "CAP_MISS" in error:
                print("FAILED Missing required capabilities")
            elif "RECEIPT_MISSING" in error:
                print("FAILED Missing access receipt")
            elif "LABEL_FLOW" in error:
                print("FAILED Label flow violation")
            elif "BUDGET" in error:
                print("FAILED Budget exceeded")
except Exception as e:
    print(f"Validation error: {e}")
```

### Certificate Errors

```python
try:
    result = pf.execute_plan(plan)
    certificate = result.certificate
    
    if certificate.non_interference == "failed":
        # Log violation
        pf.log_violation(
            certificate_id=certificate.certificate_id,
            reason="NI_FAILED",
            details=certificate.evidence_chain
        )
        
        # Block response or apply additional filtering
        response = apply_additional_filtering(result.response)
        
except Exception as e:
    print(f"Execution error: {e}")
```

## Advanced Configuration

### Custom Policy Rules

```python
# Define custom policy rules
custom_policy = {
    "max_tokens": 500,
    "temperature": 0.3,
    "forbidden_patterns": [
        r"\b\d{3}-\d{2}-\d{4}\b",  # SSN pattern
        r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b"  # Email pattern
    ],
    "allowed_domains": ["acme.com", "trusted-partner.com"],
    "content_filters": ["pii", "secrets", "malicious_code"]
}

# Apply policy to plan
plan.constraints.policy = custom_policy
```

### Multi-Tenant Support

```python
# Set tenant context
pf.set_tenant("acme_corp")

# Create tenant-specific plan
plan = Plan(
    plan_id=f"openai_call_{tenant}_{timestamp}",
    tenant=tenant,
    subject=Subject(
        id=user_id,
        caps=get_tenant_capabilities(tenant, user_id)
    ),
    # ... rest of plan configuration
)
```

## Monitoring and Alerting

### Setting Up Alerts

```python
# Configure alerting for violations
pf.set_alert_handler(
    on_ni_failure=lambda cert: send_alert("NI_FAILED", cert),
    on_receipt_missing=lambda plan: send_alert("RECEIPT_MISSING", plan),
    on_budget_exceeded=lambda plan: send_alert("BUDGET_EXCEEDED", plan)
)

def send_alert(alert_type, data):
    # Send to your monitoring system
    print(f"🚨 {alert_type}: {data}")
```

### Metrics Collection

```python
# Collect metrics for monitoring
metrics = {
    "total_calls": pf.get_metric("total_calls"),
    "ni_pass_rate": pf.get_metric("ni_pass_rate"),
    "avg_latency": pf.get_metric("avg_latency"),
    "error_rate": pf.get_metric("error_rate")
}

print(f"Metrics: {metrics}")
```

## Best Practices

### 1. Always Quote User Input

```python
# PASSED Correct - quoted user input
user_input = {
    "content": "{{user_message}}",
    "quoted": True
}

# FAILED Incorrect - unquoted user input
user_input = {
    "content": user_message,
    "quoted": False  # This will be rejected
}
```

### 2. Validate Receipts Before Use

```python
# Always validate receipts
receipt = pf.get_receipt(receipt_id)
if not pf.validate_receipt(receipt):
    raise ValueError("Invalid receipt")
```

### 3. Check Certificates After Calls

```python
# Always check the certificate
result = pf.execute_plan(plan)
if result.certificate.non_interference != "passed":
    # Handle violation
    handle_ni_violation(result.certificate)
```

### 4. Use Proper Channel Classification

```python
# System prompts are trusted
system_prompt = {
    "hash": "sha256:system_hash",
    "policy_hash": "sha256:policy_hash"
}

# User input is untrusted
user_input = {
    "content_hash": "sha256:user_hash",
    "quoted": True
}
```

## Troubleshooting

### Common Issues

1. **Plan Validation Fails**
   - Check that all required capabilities are present
   - Ensure receipts are valid and unexpired
   - Verify label flow is correct

2. **NI Certificate Fails**
   - Review input channel classification
   - Check that untrusted content is properly quoted
   - Verify system prompts haven't been modified

3. **Receipt Validation Fails**
   - Ensure receipt hasn't expired
   - Check that receipt covers the correct partition
   - Verify receipt signature

### Debug Mode

```python
# Enable debug mode for detailed logging
pf.set_debug_mode(True)

# This will show detailed validation steps
validation = pf.validate_plan(plan)
```

## Links

- [API Reference](/docs/api/)
- [Policy Configuration](/docs/policy/)
- [Receipt Management](/docs/receipts/)
- [Certificate Validation](/docs/certificates/)
- [Channel Classification](/docs/policy/multi_channel.md) 