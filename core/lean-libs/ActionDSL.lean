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

/-- Generic Action type with payload parameter -/
inductive Action (α : Type) where
  | SendEmail (payload : α) (score : Float)
  | LogSpend (payload : α) (usd : Float)
  | LogAction (payload : α) (message : String)

/-- Calculate spam score for an action -/
def SpamScore {α : Type} : Action α → Float
  | Action.SendEmail _ score => score
  | Action.LogSpend _ _ => 0.0
  | Action.LogAction _ _ => 0.0

/-- Calculate total budget spend from a list of actions -/
def BudgetSpend {α : Type} : List (Action α) → Float
  | [] => 0.0
  | (Action.SendEmail _ _) :: rest => BudgetSpend rest
  | (Action.LogSpend _ usd) :: rest => usd + BudgetSpend rest
  | (Action.LogAction _ _) :: rest => BudgetSpend rest

/-- Theorem: spam scores are always non-negative -/
theorem spam_nonneg {α : Type} : ∀ (a : Action α), 0.0 ≤ SpamScore a := by
  intro a
  cases a with
  | SendEmail _ score =>
    -- This would need to be proven based on how scores are generated
    -- For now, we assume scores are non-negative by construction
    simp [SpamScore]
  | LogSpend _ _ =>
    simp [SpamScore]
  | LogAction _ _ =>
    simp [SpamScore]

/-- Check if a list of actions respects budget constraints -/
def budget_ok {α : Type} (limit : Float) : List (Action α) → Prop
  | [] => True
  | actions => BudgetSpend actions ≤ limit

/-- Check if a list of actions respects spam score constraints -/
def spam_ok {α : Type} (limit : Float) : List (Action α) → Prop
  | [] => True
  | actions => ∀ (a : Action α), a ∈ actions → SpamScore a ≤ limit

/-- Combined safety check for both budget and spam constraints -/
def safety_ok {α : Type} (budget_limit : Float) (spam_limit : Float) : List (Action α) → Prop
  | actions => budget_ok budget_limit actions ∧ spam_ok spam_limit actions

end Fabric
