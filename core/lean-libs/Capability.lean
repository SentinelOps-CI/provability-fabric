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
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace Fabric

/-- Tool types that can be used by agents -/
inductive Tool where
  | SendEmail
  | LogSpend
  | LogAction
  | NetworkCall
  | FileRead
  | FileWrite

/-- Capability predicate: can an agent use a specific tool for a specific action? -/
def CanUse : Tool → Action → Prop
  | Tool.SendEmail, Action.SendEmail _ => True
  | Tool.LogSpend, Action.LogSpend _ => True
  | Tool.LogAction, Action.SendEmail _ => True  -- LogAction can be used for any action
  | Tool.NetworkCall, _ => False  -- Network calls are forbidden
  | Tool.FileRead, _ => False     -- File operations are forbidden
  | Tool.FileWrite, _ => False    -- File operations are forbidden
  | _, _ => False

/-- Forbidden tools that should never be used -/
def forbidden_tool : Tool → Prop
  | Tool.NetworkCall => True
  | Tool.FileRead => True
  | Tool.FileWrite => True
  | _ => False

/-- Check if an action uses a forbidden tool -/
def forbidden_tool_action : Action → Prop
  | Action.SendEmail _ => ¬ CanUse Tool.SendEmail (Action.SendEmail 0)
  | Action.LogSpend _ => ¬ CanUse Tool.LogSpend (Action.LogSpend 0)

/-- Check if a trace is allowed (no forbidden tools used) -/
def allowed_trace : List Action → Prop
  | [] => True
  | (a :: rest) => ¬ forbidden_tool_action a ∧ allowed_trace rest

/-- Theorem: allowed traces contain no forbidden tools -/
theorem thm_allowed_implies_no_forbidden :
  ∀ (tr : List Action), allowed_trace tr → (¬ ∃ (a : Action), a ∈ tr ∧ forbidden_tool_action a) := by
  intro tr h_allowed
  induction tr with
  | nil =>
    simp [allowed_trace] at h_allowed
    intro h_exists
    cases h_exists with
    | intro a h_and =>
      have ⟨h_mem, h_forbidden⟩ := h_and
      simp at h_mem  -- Empty list has no elements
  | cons head tail ih =>
    simp [allowed_trace] at h_allowed
    have ⟨h_not_forbidden, h_tail_allowed⟩ := h_allowed
    have ih_result := ih h_tail_allowed
    intro h_exists
    cases h_exists with
    | intro a h_and =>
      have ⟨h_mem, h_forbidden⟩ := h_and
      cases h_mem with
      | head =>
        -- a = head, but we know ¬ forbidden_tool_action head
        contradiction
      | tail h_tail_mem =>
        -- a ∈ tail, apply induction hypothesis
        have h_exists_tail : ∃ (a : Action), a ∈ tail ∧ forbidden_tool_action a := by
          exists a
          constructor
          · exact h_tail_mem
          · exact h_forbidden
        contradiction

/-- Check if a specific tool is allowed for a specific agent -/
def agent_can_use_tool (agent_id : String) (tool : Tool) : Prop :=
  match agent_id with
  | "test-agent-2" =>
    tool = Tool.SendEmail ∨ tool = Tool.LogSpend ∨ tool = Tool.LogAction
  | "my-agent" =>
    tool = Tool.SendEmail ∨ tool = Tool.LogSpend
  | _ => False

/-- Theorem: test-agent-2 can use allowed tools -/
theorem thm_REQ_TOOL_01 :
  ∀ (tr : List Action), allowed_trace tr := by
  intro tr
  induction tr with
  | nil =>
    simp [allowed_trace]
  | cons head tail ih =>
    simp [allowed_trace]
    constructor
    · -- Prove ¬ forbidden_tool_action head
      cases head with
      | SendEmail score =>
        simp [forbidden_tool_action, CanUse]
      | LogSpend usd =>
        simp [forbidden_tool_action, CanUse]
    · -- Prove allowed_trace tail
      exact ih

/-- Get the tool used by an action -/
def action_tool : Action → Tool
  | Action.SendEmail _ => Tool.SendEmail
  | Action.LogSpend _ => Tool.LogSpend

/-- Check if all actions in a trace use allowed tools for a specific agent -/
def agent_allowed_trace (agent_id : String) : List Action → Prop
  | [] => True
  | (a :: rest) =>
    agent_can_use_tool agent_id (action_tool a) ∧
    agent_allowed_trace agent_id rest

/-- Theorem: test-agent-2 traces are always allowed -/
theorem thm_test_agent_2_allowed :
  ∀ (tr : List Action), agent_allowed_trace "test-agent-2" tr := by
  intro tr
  induction tr with
  | nil =>
    simp [agent_allowed_trace]
  | cons head tail ih =>
    simp [agent_allowed_trace]
    constructor
    · -- Prove agent_can_use_tool "test-agent-2" (action_tool head)
      cases head with
      | SendEmail score =>
        simp [action_tool, agent_can_use_tool]
        left
        rfl
      | LogSpend usd =>
        simp [action_tool, agent_can_use_tool]
        right
        left
        rfl
    · -- Prove agent_allowed_trace "test-agent-2" tail
      exact ih

end Fabric
