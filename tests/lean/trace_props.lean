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

namespace TraceProps

open Fabric

-- Test data: small traces for unit testing
def empty_trace : List Action := []
def single_email_trace : List Action := [Action.SendEmail 5]
def single_spend_trace : List Action := [Action.LogSpend 100]
def mixed_trace : List Action := [Action.SendEmail 3, Action.LogSpend 150, Action.SendEmail 7]
def complex_trace : List Action := [Action.LogSpend 50, Action.SendEmail 2, Action.LogSpend 200, Action.SendEmail 1]

-- Unit tests for total_spend concatenation
theorem test_total_spend_concat_empty :
  total_spend (empty_trace ++ empty_trace) = total_spend empty_trace + total_spend empty_trace := by
  simp [empty_trace, total_spend, List.nil_append]

theorem test_total_spend_concat_single :
  total_spend (single_email_trace ++ single_spend_trace) = total_spend single_email_trace + total_spend single_spend_trace := by
  simp [single_email_trace, single_spend_trace, total_spend]
  rw [thm_total_spend_concat]

theorem test_total_spend_concat_mixed :
  total_spend (mixed_trace ++ complex_trace) = total_spend mixed_trace + total_spend complex_trace := by
  simp [mixed_trace, complex_trace, total_spend]
  rw [thm_total_spend_concat]

-- Unit tests for budget_ok prefix-closure
theorem test_budget_ok_prefix_empty :
  budget_ok (empty_trace ++ mixed_trace) → budget_ok empty_trace := by
  intro h
  exact thm_budget_ok_prefix_closed empty_trace mixed_trace h

theorem test_budget_ok_prefix_single :
  budget_ok (single_spend_trace ++ complex_trace) → budget_ok single_spend_trace := by
  intro h
  exact thm_budget_ok_prefix_closed single_spend_trace complex_trace h

-- Unit tests for budget_ok monotonicity
theorem test_budget_ok_monotone_email :
  budget_ok empty_trace → spend (Action.SendEmail 5) ≥ 0 → budget_ok (Action.SendEmail 5 :: empty_trace) := by
  intro h_budget h_spend
  exact thm_budget_ok_monotone empty_trace (Action.SendEmail 5) h_budget h_spend

theorem test_budget_ok_monotone_spend :
  budget_ok single_email_trace → spend (Action.LogSpend 100) ≥ 0 → budget_ok (Action.LogSpend 100 :: single_email_trace) := by
  intro h_budget h_spend
  exact thm_budget_ok_monotone single_email_trace (Action.LogSpend 100) h_budget h_spend

-- Unit tests for spend function
theorem test_spend_email : spend (Action.SendEmail 5) = 0 := by
  simp [spend]

theorem test_spend_log : spend (Action.LogSpend 100) = 100 := by
  simp [spend]

-- Unit tests for composition properties
theorem test_composition_associativity :
  total_spend ((empty_trace ++ single_email_trace) ++ single_spend_trace) =
  total_spend (empty_trace ++ (single_email_trace ++ single_spend_trace)) := by
  simp [empty_trace, single_email_trace, single_spend_trace, total_spend]
  rw [thm_total_spend_concat, thm_total_spend_concat, thm_total_spend_concat]
  rw [List.append_assoc]

-- Test that concatenation preserves budget constraints
theorem test_budget_concat_preservation :
  budget_ok single_email_trace → budget_ok single_spend_trace →
  budget_ok (single_email_trace ++ single_spend_trace) := by
  intro h1 h2
  -- This would use the composition theorem from test-agent-2
  -- For now, we test the basic property
  simp [single_email_trace, single_spend_trace, budget_ok]
  constructor
  · -- Prove 100 ≤ 300
    simp
  · -- Prove budget_ok [SendEmail 5]
    simp [budget_ok]

end TraceProps
