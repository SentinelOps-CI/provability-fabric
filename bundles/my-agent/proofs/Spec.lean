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

/-- My-agent specific budget configuration -/
def CFG : BudgetCfg := {
  dailyLimit := 300.0,
  spamLimit := 0.07
}

/-- My-agent specific theorem: all actions respect budget with config -/
theorem my_agent_budget_safe (tr : List Action) : budget_ok CFG tr := by
  intro tr
  induction tr with
  | nil =>
    simp [budget_ok]
  | cons head tail ih =>
    cases head with
    | SendEmail score =>
      simp [budget_ok]
      exact ih
    | LogSpend usd =>
      simp [budget_ok]
      constructor
      · -- Prove usd ≤ CFG.dailyLimit
        -- This is agent-specific logic for my-agent
        simp
      · -- Prove budget_ok CFG tail
        exact ih

end Spec
