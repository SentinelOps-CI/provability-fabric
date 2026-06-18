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
import ActionDSL

namespace Fabric

/-- Budget configuration structure for agents -/
structure BudgetCfg where
  dailyLimit : Float
  spamLimit : Float

/-- Default budget configuration -/
def defaultBudgetCfg : BudgetCfg := {
  dailyLimit := 300.0,
  spamLimit := 0.07
}

/-- Check if a list of actions respects budget constraints with config -/
def budget_ok (cfg : BudgetCfg) : List Action → Prop
  | [] => True
  | (Action.SendEmail _) :: rest => budget_ok cfg rest
  | (Action.LogSpend usd) :: rest =>
    Float.ofNat usd ≤ cfg.dailyLimit ∧ budget_ok cfg rest

/-- Check if a list of generic actions respects budget constraints with config -/
def budget_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => BudgetSpend actions ≤ cfg.dailyLimit

/-- Check if a list of generic actions respects spam constraints with config -/
def spam_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => ∀ (a : ActionG α), a ∈ actions → SpamScore a ≤ cfg.spamLimit

/-- Combined safety check for both budget and spam constraints with config -/
def safety_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | actions => budget_ok_cfg cfg actions ∧ spam_ok_cfg cfg actions

/-- Theorem: budget_ok is prefix-closed with config -/
theorem thm_budget_ok_prefix_closed_cfg (cfg : BudgetCfg) :
  ∀ (tr₁ tr₂ : List Action), budget_ok cfg (tr₁ ++ tr₂) → budget_ok cfg tr₁ := by
  intro tr₁ tr₂ h
  induction tr₁ generalizing tr₂ with
  | nil =>
    simp [budget_ok, List.nil_append]
  | cons a tr₁ ih =>
    cases a with
    | SendEmail _ =>
      simp [budget_ok, List.cons_append] at h ⊢
      exact ih tr₂ h
    | LogSpend _ =>
      simp [budget_ok, List.cons_append] at h ⊢
      obtain ⟨hle, hrest⟩ := h
      exact ⟨hle, ih tr₂ hrest⟩

/-- Theorem: budget_ok is monotone under adding non-negative spending actions with config -/
theorem thm_budget_ok_monotone_cfg (cfg : BudgetCfg) :
  ∀ (tr : List Action) (a : Action),
    budget_ok cfg tr → spend a ≥ 0 → budget_ok cfg (a :: tr) := by
  intro tr a h_budget h_spend
  cases a with
  | SendEmail _ =>
    simp [budget_ok]
    exact h_budget
  | LogSpend _ =>
    simp [budget_ok, spend]
    refine And.intro (by simp) h_budget

end Fabric
