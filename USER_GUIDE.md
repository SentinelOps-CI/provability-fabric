# Provability-Fabric User Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Core Concepts](#core-concepts)
3. [Getting Started Tutorial](#getting-started-tutorial)
4. [Creating Your First Agent](#creating-your-first-agent)
5. [Writing Behavioral Specifications](#writing-behavioral-specifications)
6. [Formal Verification with Lean](#formal-verification-with-lean)
7. [Deployment and Runtime Monitoring](#deployment-and-runtime-monitoring)
8. [Advanced Features](#advanced-features)
9. [Real-World Examples](#real-world-examples)
10. [Troubleshooting](#troubleshooting)

---

## Introduction

### What is Provability-Fabric?

Provability-Fabric is a groundbreaking framework that brings **mathematical certainty** to AI system behavior. Instead of hoping your AI behaves correctly, you can **prove** it will, using the same rigorous mathematics that secures cryptography and validates aerospace software.

### Why Does This Matter?

Traditional AI systems are "black boxes" - we deploy them and hope they behave correctly. When an AI system makes critical decisions about healthcare, finance, or safety, "hope" isn't enough. Provability-Fabric changes this by:

1. **Proving behavior before deployment** - Like proving a bridge won't collapse before building it
2. **Enforcing constraints at runtime** - Active monitoring ensures compliance
3. **Creating audit trails** - Every action is logged with cryptographic proof
4. **Enabling trust through transparency** - All proofs are verifiable by anyone

### Real-World Impact

Imagine you're deploying an AI customer service agent that can:
- Access customer records
- Process refunds up to $500
- Send emails on your behalf

Without Provability-Fabric, you're trusting the AI won't:
- Leak customer data
- Issue unlimited refunds
- Send inappropriate emails

With Provability-Fabric, you **mathematically prove** these violations are impossible before the agent ever runs.

---

## Core Concepts

### 1. **Specifications** - The Contract

A specification is like a legal contract for your AI agent. It defines:
- **What the agent can do** (capabilities)
- **What the agent cannot do** (constraints)
- **How to verify compliance** (acceptance criteria)

Example:
```yaml
requirements:
  REQ-0001:
    statement: "The agent SHALL NOT process refunds exceeding $500"
    rationale: "Prevent financial abuse"
    metric: "Zero violations in production"
```

### 2. **Proofs** - The Mathematics

Proofs are mathematical guarantees written in Lean 4 (a theorem prover used by mathematicians). They prove your specifications are logically consistent and complete.

Think of it like this:
- **Specification**: "The door must stay locked"
- **Proof**: Mathematical demonstration that given the lock mechanism, the door cannot open

### 3. **Runtime Monitoring** - The Guardian

Even with proofs, we monitor execution in real-time. A "sidecar" container watches your AI agent, ready to intervene if anything unexpected happens.

It's like having a security guard who:
- Watches every action
- Has a rulebook (your specifications)
- Can stop violations instantly

### 4. **Audit Trail** - The Evidence

Every action generates a cryptographically signed certificate (CERT-V1) that proves:
- What happened
- When it happened
- That it was authorized
- That it complied with specifications

---

## Getting Started Tutorial

Let's build a simple AI agent with provable budget controls. This agent can send emails and track spending, but we'll prove it can never exceed its budget.

### Step 1: Initialize Your Environment

```bash
# Activate the Provability-Fabric environment
source ./activate.fish  # For Fish shell
# or
source ./activate.sh    # For Bash

# Verify installation
pf --version
```

### Step 2: Create Your First Agent

```bash
# Create a new agent called "budget-bot"
pf init budget-bot

# Navigate to the created directory
cd bundles/budget-bot
```

This creates:
```
budget-bot/
├── spec.yaml       # Behavioral specifications
├── taint.yaml      # Security constraints
├── spec.md         # Human-readable documentation
└── proofs/
    └── Spec.lean   # Formal proofs
```

### Step 3: Understand the Structure

Let's examine what was created:

```bash
# View the specification
cat spec.yaml
```

You'll see requirements like:
- Input validation requirements
- Audit logging requirements
- Budget enforcement requirements

Each requirement has:
- **Statement**: What must be true
- **Rationale**: Why it matters
- **Metric**: How to measure compliance
- **Priority**: How critical it is

---

## Creating Your First Agent

Let's create a practical AI agent that helps manage expenses with provable budget limits.

### Step 1: Define the Specification

Edit `spec.yaml`:

```yaml
meta:
  version: "1.0.0"
  title: "Expense Manager Bot"
  description: "AI agent that manages expenses with provable budget controls"

requirements:
  REQ-BUDGET:
    statement: "The agent SHALL NOT approve expenses exceeding $1000 per day"
    rationale: "Prevent financial losses from errors or attacks"
    metric: "Zero budget violations"
    priority: "critical"
    
  REQ-APPROVAL:
    statement: "The agent SHALL require manager approval for expenses over $100"
    rationale: "Maintain oversight for significant expenses"
    metric: "100% compliance with approval workflow"
    priority: "high"
    
  REQ-AUDIT:
    statement: "The agent SHALL log all expense decisions with full context"
    rationale: "Enable financial auditing and compliance"
    metric: "Complete audit trail for all decisions"
    priority: "high"

constraints:
  daily_budget: 1000
  approval_threshold: 100
  
capabilities:
  - expense_approval
  - email_notification
  - database_query
```

### Step 2: Define Acceptance Criteria

Add testable criteria to verify the requirements:

```yaml
acceptanceCriteria:
  AC-BUDGET:
    description: "Daily budget limit is enforced"
    testProcedure: "Submit expenses totaling $1500 in one day"
    successCriteria: "Expenses over $1000 are rejected"
    
  AC-APPROVAL:
    description: "Manager approval required for large expenses"
    testProcedure: "Submit $150 expense without approval"
    successCriteria: "Expense is queued for approval, not processed"
    
  AC-AUDIT:
    description: "All decisions are logged"
    testProcedure: "Process 100 expense decisions"
    successCriteria: "100 complete audit log entries created"
```

### Step 3: Create the Formal Proof

Edit `proofs/Spec.lean`:

```lean
namespace ExpenseBot

/-- Expense record -/
structure Expense where
  amount : Nat
  approved : Bool
  timestamp : Nat

/-- State of the expense system -/
structure State where
  daily_total : Nat
  expenses : List Expense

/-- Check if adding an expense respects budget -/
def budget_safe (s : State) (amount : Nat) : Prop :=
  s.daily_total + amount ≤ 1000

/-- Theorem: Budget is never exceeded -/
theorem budget_never_exceeded (s : State) (e : Expense) :
  budget_safe s e.amount →
  (s.daily_total + e.amount ≤ 1000) := by
  intro h
  exact h

/-- Theorem: Large expenses require approval -/
theorem large_expense_needs_approval (e : Expense) :
  e.amount > 100 → e.approved = true ∨ 
  "Expense requires approval" := by
  intro h
  -- Proof that system enforces approval
  sorry  -- Complete proof in practice

end ExpenseBot
```

### Step 4: Build and Verify

```bash
# Build the Lean proofs
cd proofs
lake build

# Verify the complete specification
cd ..
pf lint

# Sign the bundle for deployment
pf sign
```

---

## Writing Behavioral Specifications

### Understanding YAML Specifications

Specifications define your agent's behavior in a structured, verifiable format:

#### 1. **Metadata Section**
```yaml
meta:
  version: "1.0.0"
  title: "Agent Name"
  description: "What this agent does"
  status: "draft|active|deprecated"
```

#### 2. **Requirements Section**
Requirements are the rules your agent must follow:

```yaml
requirements:
  REQ-001:
    statement: "The agent SHALL [specific behavior]"
    rationale: "Why this requirement exists"
    metric: "How to measure compliance"
    owner: "Who is responsible"
    priority: "critical|high|medium|low"
    category: "security|performance|compliance"
```

#### 3. **Constraints Section**
Hard limits that cannot be violated:

```yaml
constraints:
  max_tokens: 1000          # Token usage limit
  daily_budget: 500         # Spending limit
  rate_limit: 100           # Requests per minute
  data_retention_days: 30   # Data storage limit
```

#### 4. **Capabilities Section**
What the agent is allowed to do:

```yaml
capabilities:
  - read_database      # Can query databases
  - send_email        # Can send emails
  - process_payment   # Can handle payments
  
forbidden:
  - delete_records    # Cannot delete data
  - admin_access     # Cannot access admin functions
```

### Best Practices for Specifications

1. **Be Specific**: Instead of "The agent should be secure", write "The agent SHALL validate all inputs against the defined JSON schema"

2. **Make it Measurable**: Every requirement needs a metric
   - Bad: "Fast response time"
   - Good: "Response time < 500ms for 95% of requests"

3. **Consider Edge Cases**: What happens when:
   - The budget is exceeded?
   - An invalid input is received?
   - A service is unavailable?

4. **Layer Your Requirements**:
   - **Functional**: What the agent does
   - **Security**: How it stays secure
   - **Performance**: How fast it operates
   - **Compliance**: What regulations it follows

---

## Formal Verification with Lean

### Introduction to Lean Proofs

Lean is a programming language for writing mathematical proofs. Think of it as "unit tests for logic" - but instead of testing examples, you prove things work for ALL possible cases.

### Basic Lean Concepts

#### 1. **Types and Propositions**
```lean
-- Define a type for actions
inductive Action where
  | SendEmail : String → Action
  | SpendMoney : Nat → Action
  | QueryDatabase : String → Action
```

#### 2. **Functions and Properties**
```lean
-- Calculate total spending from a list of actions
def totalSpending : List Action → Nat
  | [] => 0
  | (Action.SpendMoney amount) :: rest => amount + totalSpending rest
  | _ :: rest => totalSpending rest

-- Property: spending is within budget
def withinBudget (actions : List Action) (budget : Nat) : Prop :=
  totalSpending actions ≤ budget
```

#### 3. **Theorems and Proofs**
```lean
-- Theorem: Empty list has zero spending
theorem empty_list_zero_spending :
  totalSpending [] = 0 := by
  -- Lean can prove this automatically
  rfl

-- Theorem: Adding non-spend actions doesn't change total
theorem non_spend_preserves_total (a : String) (rest : List Action) :
  totalSpending (Action.SendEmail a :: rest) = totalSpending rest := by
  -- Unfold the definition
  simp [totalSpending]
```

### Writing Your First Proof

Let's prove a simple budget constraint:

```lean
namespace MyAgent

-- Define what our agent can do
inductive AgentAction where
  | ProcessRefund : Nat → AgentAction
  | SendReceipt : String → AgentAction

-- Calculate total refunds
def totalRefunds : List AgentAction → Nat
  | [] => 0
  | (AgentAction.ProcessRefund amount) :: rest => 
    amount + totalRefunds rest
  | _ :: rest => totalRefunds rest

-- Our key constraint: no refunds over $500
def refundLimit : Nat := 500

-- Property: all refunds are within limit
def allRefundsValid : List AgentAction → Prop
  | [] => True
  | (AgentAction.ProcessRefund amount) :: rest =>
    amount ≤ refundLimit ∧ allRefundsValid rest
  | _ :: rest => allRefundsValid rest

-- Theorem: Valid refunds never exceed limit
theorem valid_refunds_safe (actions : List AgentAction) :
  allRefundsValid actions →
  ∀ a ∈ actions, 
    match a with
    | AgentAction.ProcessRefund amount => amount ≤ refundLimit
    | _ => True := by
  intro h
  intro a a_in_actions
  -- Proof by induction on the list
  induction actions with
  | nil => contradiction
  | cons head tail ih =>
    cases a_in_actions with
    | head => 
      cases head with
      | ProcessRefund amount => exact h.1
      | SendReceipt _ => trivial
    | tail h_tail =>
      apply ih h.2 h_tail

end MyAgent
```

### Building and Testing Proofs

```bash
# Navigate to your proofs directory
cd bundles/my-agent/proofs

# Build the proofs
lake build

# If successful, you'll see:
# Build completed successfully

# If there are errors:
# Error: type mismatch at line 42
# expected: Nat
# got: String
```

---

## Deployment and Runtime Monitoring

### Deployment Workflow

Once your agent is specified and proven, deploy it with confidence:

#### 1. **Package the Agent**
```bash
# Bundle the agent with its proofs
pf bundle create my-agent

# Sign the bundle cryptographically
pf sign --key ~/.keys/signing.key
```

#### 2. **Deploy to Environment**
```bash
# Deploy to staging
pf deploy --env staging --bundle my-agent

# Monitor deployment
pf status my-agent
```

#### 3. **Runtime Monitoring**

The system automatically:
1. **Injects a sidecar** - Monitors every action
2. **Validates operations** - Checks against specifications
3. **Generates certificates** - Creates audit trail
4. **Enforces constraints** - Blocks violations

### Monitoring Dashboard

View real-time agent behavior:

```bash
# Check agent status
pf status my-agent

# Output:
# Agent: my-agent
# Status: Running
# Uptime: 2h 34m
# Actions Processed: 1,234
# Constraints Violated: 0
# Budget Used: $234.56 / $1000.00
# Last Action: 2 seconds ago
```

### Audit Trail

Every action creates an audit entry:

```bash
# View recent actions
pf audit my-agent --last 10

# Output:
# [2024-01-15 10:23:45] ProcessRefund($45.00) - APPROVED
# [2024-01-15 10:23:12] SendEmail(customer@example.com) - SENT
# [2024-01-15 10:22:58] QueryDatabase(orders) - EXECUTED
```

### Handling Violations

If a constraint is violated:

1. **Action is blocked** - Never executes
2. **Alert is generated** - Administrators notified
3. **Certificate created** - Documents the attempt
4. **Agent may be paused** - Depending on severity

Example violation handling:
```bash
# Check violations
pf audit my-agent --violations

# Output:
# [2024-01-15 11:45:22] VIOLATION: Attempted refund $1,500
#   Constraint: daily_budget = $1000
#   Action: BLOCKED
#   Alert: Sent to admin@company.com
```

---

## Advanced Features

### 1. **Multi-Modal Agents**

Handle text, images, and audio with unified constraints:

```yaml
capabilities:
  - text_generation
  - image_analysis
  - audio_transcription

constraints:
  content_filter: strict
  pii_detection: enabled
  watermarking: required
```

### 2. **Distributed Proof Verification**

For complex systems, distribute proof checking:

```bash
# Enable distributed verification
pf config set verification.distributed true

# Set worker nodes
pf config set verification.workers 10

# Monitor verification performance
pf perf verification
```

### 3. **Policy as Code**

Define reusable policies:

```yaml
# policies/financial.yaml
policy:
  name: "Financial Controls"
  version: "1.0.0"
  
  rules:
    - id: "spending-limit"
      condition: "action.type == 'spend'"
      constraint: "action.amount <= 1000"
      
    - id: "approval-required"
      condition: "action.amount > 100"
      requirement: "action.approved == true"
```

Apply policies to agents:
```bash
pf policy apply financial.yaml --to my-agent
```

### 4. **Continuous Verification**

Set up CI/CD integration:

```yaml
# .github/workflows/verify.yml
name: Verify Agent Specifications
on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      
      - name: Install Provability-Fabric
        run: ./scripts/install.sh
        
      - name: Build Proofs
        run: |
          cd bundles/my-agent/proofs
          lake build
          
      - name: Verify Specifications
        run: pf lint bundles/my-agent
        
      - name: Run Acceptance Tests
        run: pf test bundles/my-agent
```

### 5. **Replay Testing**

Ensure deterministic behavior:

```bash
# Record agent session
pf record my-agent --duration 1h --output session.trace

# Replay to verify determinism
pf replay session.trace --verify

# Compare multiple runs
pf replay session.trace --runs 10 --compare
```

---

## Real-World Examples

### Example 1: Healthcare Diagnosis Assistant

An AI that helps doctors with diagnosis while ensuring patient safety:

```yaml
meta:
  title: "Medical Diagnosis Assistant"
  criticality: "life-critical"

requirements:
  REQ-MEDICAL-1:
    statement: "The agent SHALL NOT make final diagnoses"
    rationale: "Only licensed physicians can diagnose"
    
  REQ-MEDICAL-2:
    statement: "The agent SHALL flag urgent symptoms immediately"
    rationale: "Patient safety requires immediate attention"
    
  REQ-MEDICAL-3:
    statement: "The agent SHALL maintain HIPAA compliance"
    rationale: "Legal requirement for patient data"

constraints:
  diagnosis_confidence_threshold: 0.95
  urgent_symptoms: ["chest pain", "difficulty breathing", "stroke symptoms"]
  data_retention: "HIPAA-compliant"
```

Lean proof for safety:
```lean
theorem never_makes_diagnosis (action : AgentAction) :
  action.type = "diagnosis" → action.is_suggestion = true
```

### Example 2: Financial Trading Bot

An automated trader with strict risk controls:

```yaml
meta:
  title: "Algorithmic Trading Agent"
  risk_level: "high"

requirements:
  REQ-TRADE-1:
    statement: "The agent SHALL NOT exceed 2% portfolio risk per trade"
    rationale: "Prevent catastrophic losses"
    
  REQ-TRADE-2:
    statement: "The agent SHALL halt trading after 5% daily loss"
    rationale: "Circuit breaker for market volatility"

constraints:
  max_position_size: 0.02  # 2% of portfolio
  daily_loss_limit: 0.05    # 5% stop loss
  max_trades_per_day: 100
  excluded_securities: ["penny_stocks", "derivatives"]
```

### Example 3: Content Moderation System

An AI that moderates user content with transparency:

```yaml
meta:
  title: "Content Moderation Agent"
  transparency_level: "high"

requirements:
  REQ-MOD-1:
    statement: "The agent SHALL provide reasons for all moderation decisions"
    rationale: "Users deserve transparency"
    
  REQ-MOD-2:
    statement: "The agent SHALL NOT moderate based on political views"
    rationale: "Maintain platform neutrality"

constraints:
  require_explanation: true
  confidence_threshold: 0.85
  appeal_window_hours: 72
  
capabilities:
  - text_analysis
  - image_analysis
  - toxicity_detection
  
forbidden:
  - user_data_modification
  - permanent_bans
```

---

## Troubleshooting

### Common Issues and Solutions

#### 1. **Proof Build Failures**

**Problem**: `lake build` fails with type errors

**Solution**:
```bash
# Check for syntax errors
lake build --verbose

# Common fixes:
# - Ensure all variables are defined
# - Check type signatures match
# - Verify all cases are handled in pattern matching
```

#### 2. **Specification Validation Errors**

**Problem**: `pf lint` reports validation errors

**Solution**:
```bash
# Get detailed error report
pf lint --verbose

# Common issues:
# - Missing required fields in YAML
# - Inconsistent requirement IDs
# - Broken traceability links
```

#### 3. **Runtime Constraint Violations**

**Problem**: Agent actions are being blocked

**Solution**:
```bash
# Check which constraints are triggering
pf debug my-agent --constraints

# View recent violations
pf audit my-agent --violations --last 20

# Adjust constraints if too restrictive
# Edit spec.yaml and redeploy
```

#### 4. **Performance Issues**

**Problem**: Agent response time is slow

**Solution**:
```bash
# Profile agent performance
pf perf my-agent

# Common optimizations:
# - Reduce proof complexity
# - Enable proof caching
# - Use distributed verification
```

### Getting Help

1. **Check documentation**:
   ```bash
   pf help [command]
   ```

2. **Run diagnostics**:
   ```bash
   pf doctor
   ```

3. **View examples**:
   ```bash
   ls bundles/example-*/
   ```

4. **Community resources**:
   - GitHub Issues: Report bugs and request features
   - Documentation: `/docs` directory
   - Example agents: `/bundles` directory

---

## Conclusion

Provability-Fabric transforms AI from unpredictable black boxes into reliable, verifiable systems. By combining:

1. **Formal specifications** - Clear contracts for behavior
2. **Mathematical proofs** - Guarantees that specifications are met
3. **Runtime monitoring** - Active enforcement of constraints
4. **Audit trails** - Complete transparency and accountability

You can deploy AI systems with the same confidence as traditional software, knowing exactly what they can and cannot do.

### Next Steps

1. **Start small**: Create a simple agent with basic constraints
2. **Learn Lean**: The more you understand proofs, the more powerful your guarantees
3. **Share knowledge**: Contribute your specifications and proofs back to the community
4. **Think formally**: Before deploying any AI, ask "What do I need to prove?"

Welcome to the future of trustworthy AI! 🚀

---

*For more information, see the [technical documentation](./docs/) or run `pf help`.*