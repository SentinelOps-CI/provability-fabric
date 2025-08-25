# Provability Fabric - Policy Proofs

This directory contains the formal specifications and proofs for the Provability Fabric permission system.

## Overview

The Policy.lean file implements a unified permissions system that combines:

1. **Unified Action Space**: Single `Action` type covering tools, documents, and grants
2. **Executable Decider**: `permitD` function that returns `Bool` for runtime decisions
3. **Formal Specification**: `Permit` proposition for mathematical reasoning
4. **IFC-aware Access**: Field-level read/write with label flow control
5. **Non-interference**: Monitor state and global NI properties

## Core Components

### Principal & Context
- `Principal`: User/service with roles, org, and attributes
- `Ctx`: Runtime context including session, epoch, tenant, and attributes
- `DocId`: Document identifier with URI and version

### Actions
- `Action.Call tool`: Tool invocation (SendEmail, LogSpend, etc.)
- `Action.Read doc path`: Field-level document read
- `Action.Write doc path`: Field-level document write  
- `Action.Grant principal action`: Permission delegation

### Labels & IFC
- `Label`: Security classification (Public, Internal, Confidential, Secret)
- `Label.le`: Label ordering for information flow control
- `flowsOrDeclassified`: Check if label flows or is declassified
- `CanReadField`/`CanWriteField`: Field-level access with label checks

### World Interface
- `World α`: Abstract interface for document metadata and labels
- `getLabel`: Get document security label
- `getMeta`: Get document metadata (owner, ACL, etc.)
- `getFieldLabel`: Get field-specific security label

## Key Theorems

### Soundness
```lean
theorem soundness : ∀ (u : Principal) (a : Action) (γ : Ctx),
  permitD u a γ = true → Permit u a γ
```
**Proof**: If the executable decider returns true, then the formal specification holds.

### Completeness  
```lean
theorem completeness : ∀ (u : Principal) (a : Action) (γ : Ctx),
  Permit u a γ → permitD u a γ = true
```
**Proof**: If the formal specification holds, then the executable decider returns true.

### IFC Property
```lean
theorem read_requires_label_flow : ∀ (u : Principal) (doc : DocId) (path : List String) (γ : Ctx),
  ¬u.roles.contains "admin" ∧
  (∀ (α : Type) (world : World α) (w : α),
     match world.getLabel w doc with
     | some doc_label =>
         let user_label := Label.Internal
         ¬flowsOrDeclassified user_label doc_label γ.attributes
     | none => False) →
  permitD u (Action.Read doc path) γ = false
```
**Proof**: If label doesn't flow and no declass rule matches, read is denied.

### NI Bridge
```lean
theorem ni_bridge : ∀ (u : Principal) (a : Action) (γ : Ctx) (monitor : NIMonitor) (prefixes : List NIPrefix),
  permitD u a γ = true →
  (∀ prefix ∈ prefixes, monitor.accepts_prefix prefix) →
  GlobalNonInterference monitor prefixes
```
**Proof**: If permitD accepts and \MonNI accepts all prefixes, global non-interference holds.

## Non-Interference Monitor

### Monitor State
- `NIMonitor`: Tracks prefixes, active sessions, violations, and audit timestamps
- `NIEvent`: Individual events with input/output labels and data paths
- `NIPrefix`: Event sequences with input/output label constraints

### Acceptance Criteria
```lean
def NIMonitor.accepts_prefix (monitor : NIMonitor) (prefix : NIPrefix) : Prop :=
  monitor.active_sessions.length > 0 ∧
  ¬prefix.violates_ni ∧
  monitor.violation_count < 1000
```

### Global NI Property
```lean
def GlobalNonInterference (monitor : NIMonitor) (prefixes : List NIPrefix) : Prop :=
  ∀ prefix ∈ prefixes, monitor.accepts_prefix prefix ∧
  ∀ prefix1 prefix2 ∈ prefixes,
    prefix1.input_label = prefix2.input_label →
    prefix1.output_label = prefix2.output_label
```

## Usage Examples

### Basic Permission Check
```lean
def testPrincipal : Principal :=
  { id := "test-user", roles := ["email_user", "reader"], org := "test-org", attributes := [] }

def testCtx : Ctx :=
  { session := "session-1", epoch := 1, attributes := [], tenant := "test-tenant", timestamp := 1234567890 }

-- User can send emails
example : permitD testPrincipal (Action.Call Tool.SendEmail) testCtx = true := by
  simp [permitD, testPrincipal, testCtx]

-- User cannot make network calls
example : permitD testPrincipal (Action.Call Tool.NetworkCall) testCtx = false := by
  simp [permitD, testPrincipal, testCtx]
```

### NI Monitor Test
```lean
def testMonitor : NIMonitor :=
  { prefixes := [], active_sessions := ["session1"], violation_count := 0, last_audit := 1234567890 }

def testPrefix : NIPrefix :=
  { prefix_id := "test-prefix", events := [], input_label := Label.Internal,
    output_label := Label.Public, created_at := 1234567890, last_updated := 1234567890 }

-- Monitor accepts valid prefix
example : testMonitor.accepts_prefix testPrefix = true := by
  simp [NIMonitor.accepts_prefix, testMonitor, testPrefix]
  simp [NIPrefix.violates_ni]
```

## Building

To build the proofs:

```bash
cd proofs
lake build
```

Or from the root directory:

```bash
lake build
```

## Architecture Notes

### Spec/Decider Split
The system maintains a clear separation between:
- **Specification** (`Permit`): Mathematical proposition for reasoning
- **Decider** (`permitD`): Executable function for runtime decisions

This split enables:
- Formal verification of security properties
- Efficient runtime enforcement
- Clear audit trail of decisions

### Field-Level Access Control
Document access is controlled at the field level using:
- Path-based field identification (`List String`)
- Label flow checking with `flowsOrDeclassified`
- Integration with Merkle tree witnesses (planned)

### Epoch-Based Revocation
The context includes an `epoch` field for:
- Permission snapshot management
- Safe revocation procedures
- Finite monitor state domains

## Future Work

1. **Complete Proofs**: Finish the `sorry` placeholders with detailed proofs
2. **Witness Integration**: Add Merkle path validation to field access
3. **Declass Rules**: Implement declassification rule evaluation
4. **Performance**: Optimize the executable decider for high-throughput scenarios
5. **Integration**: Connect with ActionDSL and runtime enforcement

## References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
- [Information Flow Control](https://en.wikipedia.org/wiki/Information_flow_(information_theory))
- [Non-interference](https://en.wikipedia.org/wiki/Non-interference_(security))
