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
  dailyLimit : Nat
  spamLimit : Float

/-- Default budget configuration -/
def defaultBudgetCfg : BudgetCfg := {
  dailyLimit := 300,
  spamLimit := 0.07
}

/-- Check if a list of actions respects budget constraints with config -/
def budget_ok (cfg : BudgetCfg) : List Action → Prop
  | [] => True
  | (Action.SendEmail _) :: rest => budget_ok cfg rest
  | (Action.LogSpend usd) :: rest =>
    total_spend (Action.LogSpend usd :: rest) ≤ cfg.dailyLimit ∧ budget_ok cfg rest

/-- Check if a list of generic actions respects budget constraints with config -/
def budget_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => BudgetSpend actions ≤ (cfg.dailyLimit : Float)

/-- Check if a list of generic actions respects spam constraints with config -/
def spam_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | [] => True
  | actions => ∀ (a : ActionG α), a ∈ actions → SpamScore a ≤ cfg.spamLimit

/-- Combined safety check for both budget and spam constraints with config -/
def safety_ok_cfg {α : Type} (cfg : BudgetCfg) : List (ActionG α) → Prop
  | actions => budget_ok_cfg cfg actions ∧ spam_ok_cfg cfg actions

private theorem total_spend_append_le (tr₁ tr₂ : List Action) :
    total_spend tr₁ ≤ total_spend (tr₁ ++ tr₂) := by
  rw [thm_total_spend_concat]
  exact Nat.le_add_right _ _

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
    | LogSpend usd =>
      simp [budget_ok, List.cons_append, total_spend] at h ⊢
      obtain ⟨hle, hrest⟩ := h
      have prefix_le :
          usd + total_spend tr₁ ≤ usd + total_spend (tr₁ ++ tr₂) :=
        Nat.add_le_add_left (total_spend_append_le tr₁ tr₂) usd
      exact ⟨le_trans prefix_le hle, ih tr₂ hrest⟩

/-- Theorem: budget_ok is monotone under adding budget-respecting actions with config -/
theorem thm_budget_ok_monotone_cfg (cfg : BudgetCfg) :
  ∀ (tr : List Action) (a : Action),
    budget_ok cfg tr →
    (match a with
     | Action.LogSpend usd => total_spend (Action.LogSpend usd :: tr) ≤ cfg.dailyLimit
     | _ => True) →
    budget_ok cfg (a :: tr) := by
  intro tr a h_budget h_respects
  cases a with
  | SendEmail _ =>
    simp [budget_ok]
    exact h_budget
  | LogSpend _ =>
    simp [budget_ok]
    exact ⟨h_respects, h_budget⟩

/-- Theorem: budget_ok implies total_spend stays within the configured daily limit -/
theorem thm_budget_ok_implies_total_spend_le (cfg : BudgetCfg) (limit : Nat)
    (hlim : cfg.dailyLimit = limit) :
    ∀ (tr : List Action), budget_ok cfg tr → total_spend tr ≤ limit := by
  intro tr h
  induction tr with
  | nil =>
    simp [budget_ok, total_spend]
  | cons head tail ih =>
    cases head with
    | SendEmail _ =>
      simp [budget_ok, total_spend] at h ⊢
      exact ih h
    | LogSpend usd =>
      simp [budget_ok, total_spend] at h ⊢
      obtain ⟨h_sum, h_rest⟩ := h
      rw [hlim] at h_sum ⊢
      exact h_sum

end Fabric
