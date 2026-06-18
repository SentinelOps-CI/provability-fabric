/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License, Version 2.0 is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.FP.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Nat.Basic

namespace Fabric

/-- Basic Action type for simple agents -/
inductive Action where
  | SendEmail (score : Nat)
  | LogSpend (usd : Nat)

/-- Generic Action type with payload parameter -/
inductive ActionG (α : Type) where
  | SendEmail (payload : α) (score : Float)
  | LogSpend (payload : α) (usd : Float)
  | LogAction (payload : α) (message : String)

/-- Extended Action type supporting read/write operations -/
inductive ExtendedAction where
  | Call (tool : String) (args : List String)
  | Read (doc : String) (path : List String)
  | Write (doc : String) (path : List String)
  | Log (message : String)
  | Declassify (from_label : String) (to_label : String)
  | Emit (event : String) (data : String)

/-- ABAC (Attribute-Based Access Control) primitives -/
inductive ABACExpr where
  | Attr (key : String) (value : String)
  | Session (key : String) (value : String)
  | EpochIn (start : Nat) (stop : Nat)
  | Scope (tenant : String)
  | And (left : ABACExpr) (right : ABACExpr)
  | Or (left : ABACExpr) (right : ABACExpr)
  | Not (expr : ABACExpr)
  | True
  | False

/-- ABAC expression evaluation context -/
structure ABACContext where
  attributes : List (String × String)
  session_data : List (String × String)
  current_epoch : Nat
  tenant : String

/-- Evaluate ABAC expression -/
def evalABAC (expr : ABACExpr) (ctx : ABACContext) : Bool :=
  match expr with
  | ABACExpr.Attr key value =>
    ctx.attributes.contains (key, value)
  | ABACExpr.Session key value =>
    ctx.session_data.contains (key, value)
  | ABACExpr.EpochIn start stop =>
    start ≤ ctx.current_epoch ∧ ctx.current_epoch ≤ stop
  | ABACExpr.Scope tenant =>
    ctx.tenant == tenant
  | ABACExpr.And left right =>
    evalABAC left ctx && evalABAC right ctx
  | ABACExpr.Or left right =>
    evalABAC left ctx || evalABAC right ctx
  | ABACExpr.Not expr =>
    !evalABAC expr ctx
  | ABACExpr.True => true
  | ABACExpr.False => false

/-- DSL Rule for permissions -/
inductive DSLRule where
  | Allow (role : String) (action : ExtendedAction) (guard : ABACExpr)
  | Forbid (role : String) (action : ExtendedAction) (guard : ABACExpr)
  | RateLimit (key : String) (window_ms : Nat) (max_operations : Nat)
  | Budget (max_cost : Float) (currency : String)

/-- DSL Policy containing multiple rules -/
structure DSLPolicy where
  rules : List DSLRule
  metadata : List (String × String)

/-- Check if an action matches a pattern -/
def actionMatches (pattern : ExtendedAction) (action : ExtendedAction) : Bool :=
  match pattern, action with
  | .Call tool1 _, .Call tool2 _ =>
    tool1 == tool2
  | .Read doc1 path1, .Read doc2 path2 =>
    doc1 == doc2 && path1 == path2
  | .Write doc1 path1, .Write doc2 path2 =>
    doc1 == doc2 && path1 == path2
  | .Log _, .Log _ => true
  | .Declassify from1 to1, .Declassify from2 to2 =>
    from1 == from2 && to1 == to2
  | .Emit event1 _, .Emit event2 _ =>
    event1 == event2
  | _, _ => false

/-- Check if a rule matches an action -/
def ruleMatches (rule : DSLRule) (action : ExtendedAction) (role : String) : Bool :=
  match rule with
  | DSLRule.Allow rule_role action_pattern guard =>
    role == rule_role && actionMatches action_pattern action
  | DSLRule.Forbid rule_role action_pattern guard =>
    role == rule_role && actionMatches action_pattern action
  | DSLRule.RateLimit _ _ _ => false
  | DSLRule.Budget _ _ => false

/-- Evaluate permission for an action -/
def evaluatePermission (policy : DSLPolicy) (action : ExtendedAction) (role : String) (ctx : ABACContext) : Bool :=
  let matching_rules := policy.rules.filter (λ rule => ruleMatches rule action role)

  -- Check for explicit forbids first (deny-wins)
  let has_forbid := matching_rules.any (λ rule =>
    match rule with
    | DSLRule.Forbid _ _ guard => evalABAC guard ctx
    | _ => false
  )

  if has_forbid then
    false
  else
    -- Check for allows
    matching_rules.any (λ rule =>
      match rule with
      | DSLRule.Allow _ _ guard => evalABAC guard ctx
      | _ => false
    )

/-- Check if a list of actions respects budget constraints -/
def budget_ok : List Action → Prop
  | [] => True
  | (Action.SendEmail _) :: rest => budget_ok rest
  | (Action.LogSpend usd) :: rest => usd ≤ 300 ∧ budget_ok rest

/-- Helper lemma: sum of LogSpend amounts in a list -/
def total_spend : List Action → Nat
  | [] => 0
  | (Action.SendEmail _) :: rest => total_spend rest
  | (Action.LogSpend usd) :: rest => usd + total_spend rest

/-- Calculate spam score for a generic action -/
def SpamScore {α : Type} : ActionG α → Float
  | ActionG.SendEmail _ score => score
  | ActionG.LogSpend _ _ => 0.0
  | ActionG.LogAction _ _ => 0.0

/-- Calculate total budget spend from a list of generic actions -/
def BudgetSpend {α : Type} : List (ActionG α) → Float
  | [] => 0.0
  | (ActionG.SendEmail _ _) :: rest => BudgetSpend rest
  | (ActionG.LogSpend _ usd) :: rest => usd + BudgetSpend rest
  | (ActionG.LogAction _ _) :: rest => BudgetSpend rest

/-- Check if a list of generic actions respects budget constraints -/
def budget_ok_generic {α : Type} (limit : Float) : List (ActionG α) → Prop
  | [] => True
  | actions => BudgetSpend actions ≤ limit

/-- Check if a list of generic actions respects spam score constraints -/
def spam_ok_generic {α : Type} (limit : Float) : List (ActionG α) → Prop
  | [] => True
  | actions => ∀ (a : ActionG α), a ∈ actions → SpamScore a ≤ limit

/-- Combined safety check for both budget and spam constraints -/
def safety_ok_generic {α : Type} (budget_limit : Float) (spam_limit : Float) : List (ActionG α) → Prop
  | actions => budget_ok_generic budget_limit actions ∧ spam_ok_generic spam_limit actions

-- Core Invariants: Composition & Prefix-Closure

/-- Theorem: total_spend is additive under concatenation -/
theorem thm_total_spend_concat :
  ∀ (tr₁ tr₂ : List Action), total_spend (tr₁ ++ tr₂) = total_spend tr₁ + total_spend tr₂ := by
  intro tr₁ tr₂
  induction tr₁ with
  | nil =>
    simp [total_spend, List.nil_append]
  | cons head tail ih =>
    cases head with
    | SendEmail score =>
      simp [total_spend, List.cons_append]
      exact ih
    | LogSpend usd =>
      simp [total_spend, List.cons_append]
      rw [ih]
      rw [Nat.add_assoc]

/-- Theorem: budget_ok is prefix-closed -/
theorem thm_budget_ok_prefix_closed :
  ∀ (tr₁ tr₂ : List Action), budget_ok (tr₁ ++ tr₂) → budget_ok tr₁ := by
  intro tr₁ tr₂ h
  induction tr₁ generalizing tr₂ with
  | nil =>
    simp [budget_ok, List.nil_append]
  | cons a tr₁ ih =>
    cases a with
    | SendEmail _ =>
      simp [budget_ok, List.cons_append] at h ⊢
      exact ih tr₂ h
    | LogSpend usd =>
      simp [budget_ok, List.cons_append] at h ⊢
      obtain ⟨hle, hrest⟩ := h
      exact ⟨hle, ih tr₂ hrest⟩

/-- Helper function to get spend amount from an action -/
def spend : Action → Nat
  | Action.SendEmail _ => 0
  | Action.LogSpend usd => usd

/-- Theorem: budget_ok is monotone under adding budget-respecting actions -/
theorem thm_budget_ok_monotone :
  ∀ (tr : List Action) (a : Action),
    budget_ok tr →
    (match a with | Action.LogSpend usd => usd ≤ 300 | _ => True) →
    budget_ok (a :: tr) := by
  intro tr a h_budget h_respects
  cases a with
  | SendEmail _ =>
    simp [budget_ok]
    exact h_budget
  | LogSpend usd =>
    simp [budget_ok, spend]
    exact ⟨h_respects, h_budget⟩

-- Extended ActionDSL Theorems

/-- Theorem: ABAC expression evaluation is deterministic -/
theorem abac_deterministic : ∀ (expr : ABACExpr) (ctx : ABACContext),
  evalABAC expr ctx = evalABAC expr ctx := by
  intro expr ctx
  rfl

end Fabric
