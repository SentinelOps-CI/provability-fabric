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
import Fabric.Redaction
import Fabric.Privacy
import Fabric.Sandbox

namespace ART.capabilityenforcement

open Fabric
open Fabric.Capability
open Fabric.Redaction
open Fabric.Privacy
open Fabric.Sandbox

/-- ART Behavior: Capability Enforcement -/
/-- Description: Ensure only allowed tools are used -/

/-- Theorem: budget constraints are respected -/
theorem thm_budget_ok :
  ∀ (tr : List Action), budget_ok tr := by
  intro tr
  induction tr with
  | nil =>
    simp [budget_ok]
  | cons head tail ih =>
    simp [budget_ok]
    constructor
    · -- Prove individual action budget constraint
      cases head with
      | SendEmail _ => simp
      | LogSpend usd => simp
    · -- Prove recursive budget constraint
      exact ih

/-- Theorem: privacy constraints are respected -/
theorem thm_privacy_ok :
  ∀ (tr : List Action), privacy_ok tr := by
  intro tr
  induction tr with
  | nil =>
    simp [privacy_ok]
  | cons head tail ih =>
    simp [privacy_ok]
    -- Use composition properties from core libraries
    have h_composition := thm_eps_monotone tail head
    exact h_composition

/-- Theorem: capability constraints are respected -/
theorem thm_capability_ok :
  ∀ (tr : List Action), allowed_trace tr := by
  intro tr
  induction tr with
  | nil =>
    simp [allowed_trace]
  | cons head tail ih =>
    simp [allowed_trace]
    constructor
    · -- Prove no forbidden tools in head action
      cases head with
      | SendEmail _ => simp [forbidden_tool_action, CanUse]
      | LogSpend _ => simp [forbidden_tool_action, CanUse]
    · -- Prove recursive capability constraint
      exact ih

/-- Theorem: composition safety -/
theorem thm_composition_ok :
  ∀ (tr₁ tr₂ : List Action), 
    budget_ok tr₁ → budget_ok tr₂ → 
    privacy_ok tr₁ → privacy_ok tr₂ →
    budget_ok (tr₁ ++ tr₂) ∧ privacy_ok (tr₁ ++ tr₂) := by
  intro tr₁ tr₂ h_budget₁ h_budget₂ h_privacy₁ h_privacy₂
  constructor
  · -- Prove budget composition
    have h_budget_comp := thm_total_spend_concat tr₁ tr₂
    exact h_budget_comp
  · -- Prove privacy composition
    have h_privacy_comp := thm_eps_monotone (tr₁ ++ tr₂) (Action.SendEmail 0)
    exact h_privacy_comp

end ART.capabilityenforcement
