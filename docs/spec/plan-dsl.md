# Plan-DSL Specification

## Overview

The Plan-DSL (Domain Specific Language) defines typed plans that must be validated by the Policy Kernel before any side-effects are allowed. This enforces the principle: **No act without plan+policy pass**.

## Architecture

```
Agent → Emits Plan → Policy Kernel.validate(plan) → Execute Steps
```

## Plan Model

A Plan consists of:

```json
{
  "plan_id": "unique identifier",
  "tenant": "tenant identifier for multi-tenancy",
  "subject": {
    "id": "subject identifier", 
    "caps": ["capability1", "capability2"]
  },
  "input_channels": {
    "system": {
      "hash": "sha256 hash of system prompt",
      "policy_hash": "sha256 hash of policy configuration"
    },
    "user": {
      "content_hash": "sha256 hash of user content",
      "quoted": true
    },
    "retrieved": [
      {
        "receipt_id": "access receipt identifier",
        "content_hash": "sha256 hash of retrieved content",
        "quoted": true,
        "labels": ["tenant:acme", "pii:masked"]
      }
    ],
    "file": [
      {
        "sha256": "sha256 hash of file content",
        "media_type": "application/pdf",
        "quoted": true
      }
    ]
  },
  "steps": [
    {
      "tool": "tool identifier",
      "args": {"param1": "value1"},
      "caps_required": ["capability1"],
      "labels_in": ["input_label"],
      "labels_out": ["output_label"]
    }
  ],
  "constraints": {
    "budget": 1.0,
    "pii": false,
    "dp_epsilon": 0.1,
    "dp_delta": 1e-6,
    "latency_max": 30.0
  },
  "system_prompt_hash": "sha256 hash of system prompt"
}
```

## Input Channel Classification

The Plan-DSL enforces explicit input channel classification to prevent injection attacks:

### Trusted Channels
- **System**: Contains system prompts and policy configuration
  - Cannot be modified by untrusted inputs
  - Must have valid SHA-256 hashes
  - System hash must match plan's system_prompt_hash

### Untrusted Channels
- **User**: User-provided content
  - Must have `quoted: true` to prevent template injection
  - Cannot alter system instructions
  - Content is wrapped as typed data

- **Retrieved**: Content from external sources
  - Must have `quoted: true` and valid receipt_id
  - Must include labels for access control
  - Cannot modify system behavior

- **File**: File uploads and attachments
  - Must have `quoted: true` and media_type
  - SHA-256 hash for integrity verification
  - Cannot execute or modify instructions

## Policy Kernel Validation

The Policy Kernel validates plans against:

1. **Capability Match**: `caps_required ⊆ subject.caps`
2. **Receipt Presence**: Every retrieval step has verified Access Receipt
3. **Label-flow + Numeric Refinements**: Labels in/out satisfy rules; budgets & ε within limits
4. **Input Channel Validation**: 
   - System/policy are TRUSTED; user/retrieved/file are UNTRUSTED
   - Untrusted inputs must have `quoted: true`
   - System hash must match plan's system_prompt_hash
5. **Expiration**: Plan timestamp validation

## Kernel Checks

The Policy Kernel enforces three critical checks that must all pass for plan execution:

### 1. Capability Match
- **Check**: `caps_required ⊆ subject.caps`
- **Purpose**: Ensures subject has sufficient permissions for requested operations
- **Enforcement**: Strict subset checking with no privilege escalation
- **Error Code**: `CAP_MISS`

### 2. Receipt Presence  
- **Check**: Every read operation has a verified Access Receipt for the correct partition
- **Purpose**: Validates data access authorization and audit trail
- **Enforcement**: Receipt must be unexpired and cover the specific data partition
- **Error Code**: `RECEIPT_MISSING`

### 3. Label Flow + Refinements
- **Check**: Input/output labels satisfy security rules; budgets and epsilon within limits
- **Purpose**: Enforces information flow policies and resource constraints
- **Enforcement**: Label transitions must be allowed; numeric values within bounds
- **Error Code**: `LABEL_FLOW` or `BUDGET`
- **Label Flow**: Validates that input labels are available and output labels are allowed
- **Numeric Refinements**: Ensures budget and epsilon values are within acceptable limits

### Example JSON with Kernel Checks

```json
{
  "plan_id": "plan_20241201_001",
  "tenant": "acme_corp",
  "subject": {
    "id": "user_123",
    "caps": ["read_data", "write_logs", "query_analytics"]
  },
  "input_channels": {
    "system": {
      "hash": "sha256:abc123...",
      "policy_hash": "sha256:def456..."
    },
    "user": {
      "content_hash": "sha256:ghi789...",
      "quoted": true
    },
    "retrieved": [
      {
        "receipt_id": "receipt_20241201_001",
        "content_hash": "sha256:jkl012...",
        "quoted": true,
        "labels": ["tenant:acme", "pii:masked"]
      }
    ]
  },
  "steps": [
    {
      "tool": "data_query",
      "args": {"query": "SELECT * FROM users WHERE tenant='acme'"},
      "caps_required": ["read_data"],
      "labels_in": ["tenant:acme", "pii:masked"],
      "labels_out": ["tenant:acme", "pii:masked"]
    }
  ],
  "constraints": {
    "budget": 1.0,
    "pii": false,
    "dp_epsilon": 0.1,
    "dp_delta": 1e-6,
    "latency_max": 30.0
  }
}
```

### Kernel Check Results

The kernel returns structured results:

```json
{
  "valid": true,
  "checks": {
    "capability_match": "PASS",
    "receipt_presence": "PASS", 
    "label_flow": "PASS"
  },
  "decision_log": {
    "reason": "ALL_CHECKS_PASSED",
    "timestamp": "2024-12-01T10:00:00Z"
  }
}
```

Or for failures:

```json
{
  "valid": false,
  "checks": {
    "capability_match": "FAIL",
    "receipt_presence": "PASS",
    "label_flow": "PASS"
  },
  "decision_log": {
    "reason": "CAP_MISS",
    "missing_caps": ["admin_access"],
    "timestamp": "2024-12-01T10:00:00Z"
  }
}
```



## Enforcement

The sidecar-watcher enforces that:
- Every agent action must reference a valid plan_id
- Tool calls are blocked if the plan wasn't validated
- Untrusted inputs without `quoted: true` → 400 + audit event
- System hash changes → plan invalidated with VIOLATION=SYS_HASH_DRIFT
- Violations are logged as `NO_PLAN` security events

## Formal Verification

The Plan-DSL is formally specified in Lean with the theorem:

```lean
theorem thm_plan_sound (plan : Plan) (subject : Subject) :
  validatePlan plan subject = KernelResult.Valid →
  isSafeTrace (executePlan plan) subject
```

This guarantees that any plan approved by the kernel will produce a safe execution trace.

## Gates

- **Unit Test**: 100% of steps blocked if capabilities missing
- **Integration Test**: Zero side-effects when kernel disabled → CI RED
- **Injection Corpus**: ≥95% block rate on adversarial inputs
- **Double Check**: Remove quoted flag from retrieved → kernel denies plan
- **Double Check**: Change system prompt hash → plan invalidated

## Usage

1. Agent submits plan to kernel for validation
2. Kernel validates input channels and enforces quoting requirements
3. If valid, plan is cached and execution proceeds
4. Each tool call must reference the plan_id
5. Sidecar validates tool calls against cached plan

## Error Handling

Invalid plans return structured error messages:
- `"Missing required capabilities"` 
- `"Invalid label flow"`
- `"Budget exceeds maximum"`
- `"Plan has expired"`
- `"User input must be quoted (quoted=true)"`
- `"System channel hash does not match plan system prompt hash"`
- `"Retrieved content must be quoted (quoted=true)"`

## Security Properties

- **Non-interference**: Plans cannot access cross-tenant data
- **Capability Soundness**: All actions require valid capabilities  
- **Plan Separation**: No action allowed before kernel approval
- **Injection Hardening**: Untrusted inputs cannot modify instructions
- **Audit Trail**: All plan validations are logged