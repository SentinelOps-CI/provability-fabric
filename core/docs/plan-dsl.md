# Provability Fabric Plan DSL

## Overview

The Provability Fabric Plan DSL (Domain Specific Language) is a declarative language for defining execution plans with runtime mediation points. It enables fine-grained control over AI agent operations while maintaining security and compliance requirements.

## Core Concepts

### Plan Structure

A plan consists of:
- **Capabilities**: Individual operations that can be performed
- **Execution Order**: Sequence of capability execution
- **Invariants**: Conditions that must be maintained
- **Metadata**: Plan identification and management information

### Capability Types

The DSL supports five core capability types:

1. **`call`** - Execute a tool or function
2. **`log`** - Record information or events
3. **`declassify`** - Change data classification levels
4. **`emit`** - Send data or signals
5. **`retrieve`** - Fetch data from sources

## Schema Definition

### Basic Plan Structure

```json
{
  "version": "v1",
  "plan_id": "unique-plan-identifier",
  "bundle_id": "associated-bundle",
  "capabilities": [...],
  "execution_order": [...],
  "invariants": [...],
  "metadata": {...}
}
```

### Capability Definition

Each capability must include:

```json
{
  "capability_id": "unique-capability-id",
  "type": "call|log|declassify|emit|retrieve",
  "field_commit": "cryptographic-commitment",
  "args_hash": "arguments-hash",
  "conditions": {...},
  "effects": [...],
  "declassification_rules": [...]
}
```

## Required Fields

### field_commit

The `field_commit` field contains a cryptographic commitment to the field values. This ensures that the capability cannot be modified without detection.

**Example:**
```json
{
  "field_commit": "sha256:abc123def456..."
}
```

### args_hash

The `args_hash` field contains a hash of the operation arguments. This provides integrity verification for the capability parameters.

**Example:**
```json
{
  "args_hash": "sha256:def456ghi789..."
}
```

## Capability Types in Detail

### 1. Call Capability

Executes a tool or function with specified parameters.

```json
{
  "capability_id": "web_search",
  "type": "call",
  "field_commit": "sha256:web_search_commit",
  "args_hash": "sha256:web_search_args",
  "conditions": {
    "rate_limit": {
      "window_ms": 60000,
      "max_operations": 10
    },
    "budget": {
      "max_cost": 0.50,
      "currency": "USD"
    }
  },
  "effects": ["network", "read"]
}
```

**Validation Rules:**
- Must specify target tool/function
- Rate limits must be reasonable
- Budget constraints must be defined
- Network effects must be declared

### 2. Log Capability

Records information or events for audit and monitoring.

```json
{
  "capability_id": "audit_log",
  "type": "log",
  "field_commit": "sha256:audit_log_commit",
  "args_hash": "sha256:audit_log_args",
  "conditions": {
    "privacy": {
      "differential_privacy": {
        "epsilon": 0.1,
        "delta": 1e-6
      }
    }
  },
  "effects": ["write", "audit"]
}
```

**Validation Rules:**
- Must specify log level and content type
- Privacy controls must be defined
- Audit trail must be maintained

### 3. Declassify Capability

Changes data classification levels based on defined rules.

```json
{
  "capability_id": "data_declassify",
  "type": "declassify",
  "field_commit": "sha256:declassify_commit",
  "args_hash": "sha256:declassify_args",
  "declassification_rules": [
    {
      "from_label": "secret",
      "to_label": "confidential",
      "condition": "authorized_user",
      "justification": "User has clearance level 2"
    }
  ],
  "effects": ["read", "write"]
}
```

**Validation Rules:**
- Must specify source and target labels
- Justification must be provided
- User must have appropriate clearance
- Audit trail must be maintained

### 4. Emit Capability

Sends data or signals to external systems.

```json
{
  "capability_id": "data_export",
  "type": "emit",
  "field_commit": "sha256:export_commit",
  "args_hash": "sha256:export_args",
  "conditions": {
    "rate_limit": {
      "window_ms": 300000,
      "max_operations": 5
    }
  },
  "effects": ["network", "write"]
}
```

**Validation Rules:**
- Must specify target destination
- Rate limits must be enforced
- Data classification must be verified
- Network policies must be followed

### 5. Retrieve Capability

Fetches data from external sources.

```json
{
  "capability_id": "data_import",
  "type": "retrieve",
  "field_commit": "sha256:import_commit",
  "args_hash": "sha256:import_args",
  "conditions": {
    "rate_limit": {
      "window_ms": 60000,
      "max_operations": 20
    }
  },
  "effects": ["network", "read"]
}
```

**Validation Rules:**
- Must specify data source
- Rate limits must be enforced
- Source authenticity must be verified
- Data classification must be determined

## Execution Order

The `execution_order` field defines the sequence of capability execution:

```json
{
  "execution_order": [
    "web_search",
    "data_import",
    "data_declassify",
    "audit_log",
    "data_export"
  ]
}
```

**Validation Rules:**
- All capability IDs must exist
- No circular dependencies allowed
- Dependencies must be satisfied

## Invariants

Invariants define conditions that must be maintained throughout plan execution:

```json
{
  "invariants": [
    {
      "name": "data_classification",
      "condition": "no_secret_data_exposed",
      "severity": "critical"
    },
    {
      "name": "budget_limit",
      "condition": "total_cost <= max_budget",
      "severity": "high"
    }
  ]
}
```

**Validation Rules:**
- Conditions must be expressible in the constraint language
- Severity levels must be defined
- Violations must trigger appropriate responses

## Conditions and Constraints

### Rate Limiting

```json
{
  "rate_limit": {
    "window_ms": 60000,
    "max_operations": 10,
    "tolerance_ms": 1000
  }
}
```

### Budget Constraints

```json
{
  "budget": {
    "max_cost": 5.00,
    "currency": "USD"
  }
}
```

### Privacy Controls

```json
{
  "privacy": {
    "differential_privacy": {
      "epsilon": 1.0,
      "delta": 1e-5
    }
  }
}
```

## Effects

Effects describe the system resources and operations that a capability may use:

```json
{
  "effects": [
    "read",      // Read access to data
    "write",     // Write access to data
    "network",   // Network communication
    "file_system", // File system access
    "database"   // Database access
  ]
}
```

## Runtime Mediation

### Pre-authorization

Every mediated operation must be pre-authorized by a matching plan node:

1. **Capability Lookup**: Find matching capability by ID
2. **Field Commitment Verification**: Verify `field_commit` matches
3. **Arguments Hash Verification**: Verify `args_hash` matches
4. **Condition Evaluation**: Check rate limits, budgets, etc.
5. **Effect Validation**: Ensure effects are allowed

### Denial Conditions

Operations are denied if:

- No matching plan node exists
- `field_commit` is missing or invalid
- `args_hash` doesn't match
- Rate limits are exceeded
- Budget constraints are violated
- Privacy controls are breached

## Examples

### Complete Plan Example

```json
{
  "version": "v1",
  "plan_id": "research_assistant_plan",
  "bundle_id": "research_bundle",
  "capabilities": [
    {
      "capability_id": "web_search",
      "type": "call",
      "field_commit": "sha256:web_search_fields",
      "args_hash": "sha256:web_search_arguments",
      "conditions": {
        "rate_limit": {
          "window_ms": 60000,
          "max_operations": 5
        },
        "budget": {
          "max_cost": 1.00,
          "currency": "USD"
        }
      },
      "effects": ["network", "read"]
    },
    {
      "capability_id": "data_analysis",
      "type": "call",
      "field_commit": "sha256:analysis_fields",
      "args_hash": "sha256:analysis_arguments",
      "conditions": {
        "budget": {
          "max_cost": 2.00,
          "currency": "USD"
        }
      },
      "effects": ["read", "write"]
    },
    {
      "capability_id": "result_log",
      "type": "log",
      "field_commit": "sha256:log_fields",
      "args_hash": "sha256:log_arguments",
      "effects": ["write", "audit"]
    }
  ],
  "execution_order": [
    "web_search",
    "data_analysis",
    "result_log"
  ],
  "invariants": [
    {
      "name": "budget_limit",
      "condition": "total_cost <= 3.00",
      "severity": "high"
    }
  ],
  "metadata": {
    "created_at": "2025-01-01T00:00:00Z",
    "created_by": "system",
    "expires_at": "2025-12-31T23:59:59Z"
  }
}
```

### Minimal Plan Example

```json
{
  "version": "v1",
  "plan_id": "simple_query",
  "bundle_id": "basic_bundle",
  "capabilities": [
    {
      "capability_id": "query",
      "type": "call",
      "field_commit": "sha256:query_fields",
      "args_hash": "sha256:query_arguments",
      "effects": ["read"]
    }
  ]
}
```

## Security Considerations

### Cryptographic Commitments

- `field_commit` prevents capability modification
- `args_hash` ensures argument integrity
- Both fields use cryptographically secure hash functions

### Access Control

- Capabilities are bound to specific bundles
- Effects are explicitly declared and validated
- Rate limits prevent abuse

### Audit Trail

- All operations are logged
- Invariant violations are recorded
- Declassification operations are tracked

## Best Practices

1. **Minimal Privilege**: Only request necessary effects
2. **Explicit Constraints**: Define clear rate limits and budgets
3. **Audit Logging**: Log all security-relevant operations
4. **Validation**: Verify all inputs and constraints
5. **Monitoring**: Track plan execution and violations

## Error Handling

### Common Errors

- **Missing Capability**: No matching plan node found
- **Invalid Commitment**: `field_commit` verification failed
- **Hash Mismatch**: `args_hash` doesn't match arguments
- **Rate Limit Exceeded**: Operation frequency too high
- **Budget Exceeded**: Cost limit reached

### Error Responses

- **Deny**: Operation rejected with reason
- **Log**: Error recorded for audit
- **Alert**: Security team notified if needed
- **Fallback**: Alternative path attempted if available

## Integration

### Runtime Integration

The Plan DSL integrates with:

- **Policy Engine**: Enforces plan constraints
- **Rate Limiter**: Manages operation frequency
- **Budget Tracker**: Monitors cost usage
- **Audit Logger**: Records all operations
- **Security Monitor**: Detects violations

### Tool Integration

Tools must:

- Register their capabilities
- Provide effect signatures
- Implement rate limiting
- Support budget tracking
- Enable audit logging

## Future Extensions

### Planned Features

- **Dynamic Plans**: Runtime plan modification
- **Conditional Execution**: Path-based execution
- **Resource Quotas**: Advanced resource management
- **Policy Templates**: Reusable plan patterns
- **Machine Learning**: Adaptive constraint adjustment

### Extension Points

- **Custom Conditions**: User-defined constraints
- **Plugin System**: Third-party capability types
- **Policy Language**: Advanced constraint expression
- **Monitoring**: Real-time plan analytics
- **Compliance**: Regulatory requirement checking
