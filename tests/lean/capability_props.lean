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
import Fabric.Capability

namespace CapabilityProps

open Fabric
open Fabric.Capability

/-- Test that allowed traces contain no forbidden tools -/
theorem test_allowed_trace_no_forbidden :
  ∀ (tr : List Action), allowed_trace tr → (¬ ∃ (a : Action), a ∈ tr ∧ forbidden_tool_action a) := by
  exact thm_allowed_implies_no_forbidden

/-- Test that test-agent-2 can use allowed tools -/
theorem test_agent_2_allowed_tools :
  ∀ (tr : List Action), agent_allowed_trace "test-agent-2" tr := by
  exact thm_test_agent_2_allowed

/-- Test that forbidden tools are actually forbidden -/
theorem test_forbidden_tools_are_forbidden :
  forbidden_tool Tool.NetworkCall ∧
  forbidden_tool Tool.FileRead ∧
  forbidden_tool Tool.FileWrite := by
  constructor
  · simp [forbidden_tool]
  · constructor
    · simp [forbidden_tool]
    · simp [forbidden_tool]

/-- Test that allowed tools are not forbidden -/
theorem test_allowed_tools_not_forbidden :
  ¬ forbidden_tool Tool.SendEmail ∧
  ¬ forbidden_tool Tool.LogSpend ∧
  ¬ forbidden_tool Tool.LogAction := by
  constructor
  · simp [forbidden_tool]
  · constructor
    · simp [forbidden_tool]
    · simp [forbidden_tool]

/-- Test that action tools are correctly mapped -/
theorem test_action_tool_mapping :
  action_tool (Action.SendEmail 0) = Tool.SendEmail ∧
  action_tool (Action.LogSpend 0) = Tool.LogSpend := by
  constructor
  · simp [action_tool]
  · simp [action_tool]

/-- Test that CanUse correctly identifies allowed tool-action pairs -/
theorem test_can_use_allowed_pairs :
  CanUse Tool.SendEmail (Action.SendEmail 0) ∧
  CanUse Tool.LogSpend (Action.LogSpend 0) := by
  constructor
  · simp [CanUse]
  · simp [CanUse]

/-- Test that CanUse correctly rejects forbidden tool-action pairs -/
theorem test_can_use_forbidden_pairs :
  ¬ CanUse Tool.NetworkCall (Action.SendEmail 0) ∧
  ¬ CanUse Tool.FileRead (Action.LogSpend 0) := by
  constructor
  · simp [CanUse]
  · simp [CanUse]

/-- Test that agent capability model works correctly -/
theorem test_agent_capability_model :
  agent_can_use_tool "test-agent-2" Tool.SendEmail ∧
  agent_can_use_tool "test-agent-2" Tool.LogSpend ∧
  ¬ agent_can_use_tool "test-agent-2" Tool.NetworkCall := by
  constructor
  · simp [agent_can_use_tool]
    left
    rfl
  · constructor
    · simp [agent_can_use_tool]
      right
      left
      rfl
    · simp [agent_can_use_tool]
      intro h
      cases h with
      | inl h1 => contradiction
      | inr h2 =>
        cases h2 with
        | inl h3 => contradiction
        | inr h4 => contradiction

end CapabilityProps
