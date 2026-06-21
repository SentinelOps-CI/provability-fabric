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

open Fabric

/-- Test-agent-2 specific budget configuration -/
def CFG : BudgetCfg := {
  dailyLimit := 300,
  spamLimit := 0.07
}

/-- REQ-0003: configured daily limit matches the enforced spend ceiling -/
theorem test_agent_2_daily_limit_cfg :
    CFG.dailyLimit = 300 := rfl

/-- REQ-0003: budget_ok implies spend stays within the agent-configured ceiling -/
theorem test_agent_2_budget_verification (tr : List Action) (h : budget_ok CFG tr) :
    total_spend tr ≤ CFG.dailyLimit :=
  thm_budget_ok_implies_total_spend_le CFG CFG.dailyLimit rfl tr h

end Spec
