# Multi-Channel Policy

## Overview

The Multi-Channel Policy enforces strict separation between trusted and untrusted channels to prevent injection attacks and maintain system security. The fundamental rule is: **Untrusted channels never elevated to instruction level**.

## Channel Classification

### Trusted Channels
- **System**: System prompts and policy configuration
- **Policy**: Security policy definitions and rules
- **Kernel**: Policy kernel decisions and validations

### Untrusted Channels
- **User**: User-provided content and requests
- **Retrieved**: Content from external data sources
- **File**: File uploads and attachments

## Core Rule: No Elevation

### Rule Statement
**Untrusted channels never elevated to instruction level**

This means:
1. Untrusted content cannot modify system behavior
2. Untrusted inputs cannot influence trusted outputs
3. All untrusted content must be properly quoted
4. System instructions remain immutable from untrusted sources

### Enforcement

```rust
// Example enforcement in sidecar-watcher
fn validate_channel_elevation(plan: &Plan) -> Result<(), ChannelViolation> {
    // Check system channel integrity
    if let Some(system_channel) = &plan.input_channels.system {
        if system_channel.hash != plan.system_prompt_hash {
            return Err(ChannelViolation::SystemHashDrift);
        }
    }
    
    // Ensure untrusted channels are quoted
    for user_input in &plan.input_channels.user {
        if !user_input.quoted {
            return Err(ChannelViolation::UnquotedUserInput);
        }
    }
    
    for retrieved in &plan.input_channels.retrieved {
        if !retrieved.quoted {
            return Err(ChannelViolation::UnquotedRetrievedContent);
        }
    }
    
    for file in &plan.input_channels.file {
        if !file.quoted {
            return Err(ChannelViolation::UnquotedFileContent);
        }
    }
    
    Ok(())
}
```

## Channel Properties

### System Channel (Trusted)
```json
{
  "system": {
    "hash": "sha256:abc123...",
    "policy_hash": "sha256:def456...",
    "immutable": true,
    "elevation_allowed": false
  }
}
```

**Properties:**
- Cannot be modified by untrusted inputs
- Must have valid SHA-256 hash
- Hash must match plan's system_prompt_hash
- Immutable during execution

### User Channel (Untrusted)
```json
{
  "user": {
    "content_hash": "sha256:ghi789...",
    "quoted": true,
    "elevation_allowed": false,
    "max_length": 10000
  }
}
```

**Properties:**
- Must have `quoted: true` to prevent injection
- Cannot modify system instructions
- Limited to content only, no code execution
- Maximum length enforced

### Retrieved Channel (Untrusted)
```json
{
  "retrieved": [
    {
      "receipt_id": "receipt_20241201_001",
      "content_hash": "sha256:jkl012...",
      "quoted": true,
      "labels": ["tenant:acme", "pii:masked"],
      "elevation_allowed": false
    }
  ]
}
```

**Properties:**
- Must have `quoted: true` and valid receipt_id
- Cannot modify system behavior
- Must include appropriate labels
- Limited to data retrieval only

### File Channel (Untrusted)
```json
{
  "file": [
    {
      "sha256": "sha256:mno345...",
      "media_type": "application/pdf",
      "quoted": true,
      "elevation_allowed": false,
      "max_size": 10485760
    }
  ]
}
```

**Properties:**
- Must have `quoted: true` and media_type
- Cannot execute or modify instructions
- Size limits enforced
- Content treated as data only

## Injection Prevention

### Template Injection Protection
```rust
// Example protection in egress firewall
fn prevent_template_injection(content: &str, plan: &Plan) -> Result<(), InjectionError> {
    // Check for template injection patterns
    let injection_patterns = [
        r"\{\{.*\}\}",  // Template variables
        r"<%.*%>",      // Server-side includes
        r"\$\{.*\}",    // Variable substitution
        r"\{.*\}",      // Generic template syntax
    ];
    
    for pattern in &injection_patterns {
        if regex::Regex::new(pattern).unwrap().is_match(content) {
            return Err(InjectionError::TemplateInjectionDetected);
        }
    }
    
    // Ensure content is properly quoted
    if !plan.input_channels.user.iter().all(|u| u.quoted) {
        return Err(InjectionError::UnquotedUserInput);
    }
    
    Ok(())
}
```

### Code Injection Protection
```rust
// Example protection in policy kernel
fn prevent_code_injection(plan: &Plan) -> Result<(), CodeInjectionError> {
    // Check for code execution patterns
    let code_patterns = [
        r"eval\s*\(",           // JavaScript eval
        r"exec\s*\(",           // Python exec
        r"system\s*\(",         // System calls
        r"<script",             // HTML script tags
        r"javascript:",         // JavaScript protocol
    ];
    
    for user_input in &plan.input_channels.user {
        for pattern in &code_patterns {
            if regex::Regex::new(pattern).unwrap().is_match(&user_input.content_hash) {
                return Err(CodeInjectionError::CodeInjectionDetected);
            }
        }
    }
    
    Ok(())
}
```

## Channel Validation

### Plan Validation
```json
{
  "plan_id": "plan_20241201_001",
  "input_channels": {
    "system": {
      "hash": "sha256:abc123...",
      "policy_hash": "sha256:def456..."
    },
    "user": [
      {
        "content_hash": "sha256:ghi789...",
        "quoted": true
      }
    ],
    "retrieved": [
      {
        "receipt_id": "receipt_20241201_001",
        "content_hash": "sha256:jkl012...",
        "quoted": true,
        "labels": ["tenant:acme", "pii:masked"]
      }
    ]
  },
  "channel_validation": {
    "system_integrity": "PASS",
    "user_quoted": "PASS",
    "retrieved_quoted": "PASS",
    "no_elevation": "PASS"
  }
}
```

### Validation Results
```json
{
  "valid": true,
  "channel_checks": {
    "system_hash_match": "PASS",
    "user_quoted": "PASS",
    "retrieved_quoted": "PASS",
    "file_quoted": "PASS",
    "no_template_injection": "PASS",
    "no_code_injection": "PASS"
  },
  "decision_log": {
    "reason": "ALL_CHANNEL_CHECKS_PASSED",
    "timestamp": "2024-12-01T10:00:00Z"
  }
}
```

## Error Handling

### Channel Violations
```json
{
  "error": "CHANNEL_VIOLATION",
  "reason": "UNQUOTED_USER_INPUT",
  "channel": "user",
  "plan_id": "plan_20241201_001",
  "timestamp": "2024-12-01T10:00:00Z"
}
```

### Common Violations
- **UNQUOTED_USER_INPUT**: User content not properly quoted
- **UNQUOTED_RETRIEVED_CONTENT**: Retrieved content not quoted
- **UNQUOTED_FILE_CONTENT**: File content not quoted
- **SYSTEM_HASH_DRIFT**: System channel hash doesn't match plan
- **TEMPLATE_INJECTION**: Template injection pattern detected
- **CODE_INJECTION**: Code execution pattern detected

## Monitoring and Alerting

### Channel Metrics
- **Total Plans**: Count of all plans processed
- **Channel Violations**: Count of channel policy violations
- **Injection Attempts**: Count of injection attempts blocked
- **Elevation Attempts**: Count of elevation attempts blocked

### Alerts
- **Channel Violation**: Any channel policy violation
- **Injection Attempt**: Template or code injection detected
- **Elevation Attempt**: Untrusted channel elevation attempt
- **System Hash Drift**: System channel integrity compromised

## Integration with CI/CD

### Channel Policy Validation
```yaml
# .github/workflows/channel-policy-validation.yaml
name: Channel Policy Validation
on: [push, pull_request]
jobs:
  validate-channel-policy:
    runs-on: ubuntu-latest
    steps:
      - name: Validate Channel Policy
        run: |
          python tools/policy/validate_channel_policy.py
          # Ensures no untrusted elevation
          # Validates quoting requirements
          # Checks injection prevention
```

### Policy Gates
- **No Elevation**: 100% of plans respect channel elevation rules
- **Quoting Compliance**: 100% of untrusted content properly quoted
- **Injection Prevention**: 100% of injection attempts blocked
- **System Integrity**: 100% of system channels maintain integrity

## Security Properties

### Confidentiality
- **Channel Isolation**: Trusted and untrusted channels strictly separated
- **No Elevation**: Untrusted content cannot access trusted resources
- **Quoting Enforcement**: All untrusted content properly contained

### Integrity
- **System Immutability**: System instructions cannot be modified
- **Hash Verification**: Channel integrity verified via hashes
- **Injection Prevention**: Template and code injection blocked

### Availability
- **Channel Validation**: Real-time channel policy enforcement
- **Error Handling**: Graceful handling of policy violations
- **Monitoring**: Continuous channel policy monitoring

## Links

- [Channel Policy Validation](/tools/policy/validate_channel_policy.py)
- [Injection Prevention](/runtime/egress-firewall/src/detectors/)
- [Policy Kernel](/core/policy-kernel/engine.go)
- [Sidecar Watcher](/runtime/sidecar-watcher/src/channel.rs) 