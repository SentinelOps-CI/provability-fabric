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
  dailyLimit := 300,
  spamLimit := 0.07
}

/-- Test-new-user-agent specific theorem: budget constraint verification with config -/
theorem test_user_budget_verification :
    ∀ (tr : List Action), budget_ok CFG tr → total_spend tr ≤ 300 :=
  fun tr h => thm_budget_ok_implies_total_spend_le CFG 300 (by simp [CFG]) tr h

end Spec
