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

import Fabric

namespace Spec

-- Import core definitions from ActionDSL
open Fabric

/-- Test-new-user-agent specific budget configuration -/
def CFG : BudgetCfg := {
  dailyLimit := 300.0,
  spamLimit := 0.07
}

/-- Test-new-user-agent specific theorem: budget constraint verification with config -/
theorem test_user_budget_verification : ∀ (tr : List Action), budget_ok CFG tr → total_spend tr ≤ 300 := by
  intro tr
  induction tr with
  | nil =>
    simp [budget_ok, total_spend]
    exact le_refl 0
  | cons head tail ih =>
    cases head with
    | SendEmail score =>
      simp [budget_ok, total_spend]
      exact ih
    | LogSpend usd =>
      simp [budget_ok, total_spend]
      intro h
      have ⟨h1, h2⟩ := h
      have ih_result := ih h2
      have add_le : usd + total_spend tail ≤ usd + 300 := by
        apply add_le_add_left
        exact ih_result
      have usd_le_300 : usd ≤ 300 := h1
      have usd_plus_300_le_600 : usd + 300 ≤ 300 + 300 := by
        apply add_le_add_right
        exact usd_le_300
      have usd_plus_300_le_300 : usd + 300 ≤ 300 := by
        simp at usd_plus_300_le_600
        exact usd_plus_300_le_600
      exact le_trans add_le usd_plus_300_le_300

end Spec
