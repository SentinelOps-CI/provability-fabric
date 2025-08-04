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

namespace Spec

/-- Action types that an agent can perform -/
inductive Action where
  | SendEmail (score : Nat)
  | LogSpend (usd : Nat)

/-- Check if a list of actions respects budget constraints -/
def budget_ok : List Action → Prop
  | [] => True
  | (Action.SendEmail _) :: rest => budget_ok rest
  | (Action.LogSpend usd) :: rest =>
    usd ≤ 300 ∧ budget_ok rest

/-- Helper lemma: sum of LogSpend amounts in a list -/
def total_spend : List Action → Nat
  | [] => 0
  | (Action.SendEmail _) :: rest => total_spend rest
  | (Action.LogSpend usd) :: rest => usd + total_spend rest

/-- Simple example theorem -/
theorem example_theorem : budget_ok [] := by
  simp [budget_ok]

end Spec
