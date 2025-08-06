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

## Policy Kernel Validation

The Policy Kernel validates plans against:

1. **Capability Match**: `caps_required ⊆ subject.caps`
2. **ABAC Check**: Tenant/label-based access control
3. **Label Flow**: Input labels ⊆ output policy 
4. **Numeric Refinements**: Budget, ε, latency limits
5. **Expiration**: Plan timestamp validation

## Enforcement

The sidecar-watcher enforces that:
- Every agent action must reference a valid plan_id
- Tool calls are blocked if the plan wasn't validated
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
- **Double Check**: Remove required capability → kernel denies with 403

## Usage

1. Agent submits plan to kernel for validation
2. Kernel returns validation result
3. If valid, plan is cached and execution proceeds
4. Each tool call must reference the plan_id
5. Sidecar validates tool calls against cached plan

## Error Handling

Invalid plans return structured error messages:
- `"Missing required capabilities"` 
- `"Invalid label flow"`
- `"Budget exceeds maximum"`
- `"Plan has expired"`

## Security Properties

- **Non-interference**: Plans cannot access cross-tenant data
- **Capability Soundness**: All actions require valid capabilities  
- **Plan Separation**: No action allowed before kernel approval
- **Audit Trail**: All plan validations are logged