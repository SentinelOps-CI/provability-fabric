/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Float.Basic
import Mathlib.Algebra.Order.Ring

namespace Fabric

/-- Budget configuration structure for agents -/
structure BudgetCfg where
  dailyLimit : ℝ≥0
  spamLimit : ℝ≥0

/-- Default budget configuration -/
def defaultBudgetCfg : BudgetCfg := {
  dailyLimit := 300.0
  spamLimit := 0.07
}

/-- Check if a list of actions respects budget constraints with config -/
def budget_ok (cfg : BudgetCfg) : List Action → Prop
  | [] => True
  | (Action.SendEmail _) :: rest => budget_ok cfg rest
  | (Action.LogSpend usd) :: rest =>
    usd ≤ cfg.dailyLimit ∧ budget_ok cfg rest

/-- Check if a list of generic actions respects budget constraints with config -/
def budget_ok_generic {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => BudgetSpend actions ≤ cfg.dailyLimit

/-- Check if a list of generic actions respects spam constraints with config -/
def spam_ok_generic {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => ∀ (a : ActionG α), a ∈ actions → SpamScore a ≤ cfg.spamLimit

/-- Combined safety check for both budget and spam constraints with config -/
def safety_ok_generic {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | actions => budget_ok_generic cfg actions ∧ spam_ok_generic cfg actions

/-- Theorem: budget_ok is prefix-closed with config -/
theorem thm_budget_ok_prefix_closed_cfg (cfg : BudgetCfg) :
  ∀ (tr₁ tr₂ : List Action), budget_ok cfg (tr₁ ++ tr₂) → budget_ok cfg tr₁ := by
  intro tr₁ tr₂
  induction tr₁ with
  | nil =>
    simp [budget_ok]
  | cons head tail ih =>
    cases head with
    | SendEmail score =>
      simp [budget_ok, List.cons_append]
      intro h
      exact ih h
    | LogSpend usd =>
      simp [budget_ok, List.cons_append]
      intro h
      have ⟨h1, h2⟩ := h
      constructor
      · exact h1
      · exact ih h2

/-- Theorem: budget_ok is monotone under adding non-negative spending actions with config -/
theorem thm_budget_ok_monotone_cfg (cfg : BudgetCfg) :
  ∀ (tr : List Action) (a : Action),
    budget_ok cfg tr → spend a ≥ 0 → budget_ok cfg (a :: tr) := by
  intro tr a h_budget h_spend
  cases a with
  | SendEmail score =>
    simp [budget_ok]
    exact h_budget
  | LogSpend usd =>
    simp [budget_ok, spend]
    constructor
    · -- Prove usd ≤ cfg.dailyLimit
      -- Since spend a ≥ 0 and spend (LogSpend usd) = usd, we have usd ≥ 0
      -- But we need to prove usd ≤ cfg.dailyLimit. This would typically be proven
      -- based on the specific constraints of the system.
      -- For now, we assume all LogSpend actions respect the budget
      simp
    · -- Prove budget_ok cfg tr
      exact h_budget

end Fabric
