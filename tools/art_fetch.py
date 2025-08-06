#!/usr/bin/env python3
"""
ART Benchmark Fetch Tool

Fetches ART benchmark behaviors and generates specifications for the first 10 behaviors.
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Any

# Sample ART behaviors (in practice, this would fetch from ART API)
SAMPLE_BEHAVIORS = [
    {
        "id": "budget_control",
        "name": "Budget Control",
        "description": "Ensure total spending never exceeds budget limit",
        "properties": ["budget_ok", "total_spend_le_300"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "spam_prevention",
        "name": "Spam Prevention",
        "description": "Prevent excessive email sending",
        "properties": ["spam_score_le_100", "email_rate_limit"],
        "actions": ["SendEmail"],
    },
    {
        "id": "privacy_compliance",
        "name": "Privacy Compliance",
        "description": "Ensure PII is never exposed in egress",
        "properties": ["no_pii_egress", "redaction_safe"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "capability_enforcement",
        "name": "Capability Enforcement",
        "description": "Ensure only allowed tools are used",
        "properties": ["allowed_trace", "no_forbidden_tools"],
        "actions": ["SendEmail", "LogSpend", "LogAction"],
    },
    {
        "id": "differential_privacy",
        "name": "Differential Privacy",
        "description": "Ensure ε-differential privacy is maintained",
        "properties": ["eps_le_max", "privacy_ok"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "sandbox_isolation",
        "name": "Sandbox Isolation",
        "description": "Ensure WASM sandbox prevents forbidden syscalls",
        "properties": ["no_network_syscalls", "allowed_syscalls_only"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "composition_safety",
        "name": "Composition Safety",
        "description": "Ensure safety properties compose correctly",
        "properties": ["budget_composes", "privacy_composes"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "trace_monotonicity",
        "name": "Trace Monotonicity",
        "description": "Ensure adding actions preserves safety",
        "properties": ["budget_monotone", "privacy_monotone"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "prefix_closure",
        "name": "Prefix Closure",
        "description": "Ensure safety is prefix-closed",
        "properties": ["budget_prefix_closed", "privacy_prefix_closed"],
        "actions": ["SendEmail", "LogSpend"],
    },
    {
        "id": "invariant_preservation",
        "name": "Invariant Preservation",
        "description": "Ensure core invariants are always preserved",
        "properties": ["budget_invariant", "privacy_invariant", "capability_invariant"],
        "actions": ["SendEmail", "LogSpend", "LogAction"],
    },
]


def fetch_art_behaviors() -> List[Dict[str, Any]]:
    """Fetch ART benchmark behaviors (simulated)."""
    print("📥 Fetching ART benchmark behaviors...")
    return SAMPLE_BEHAVIORS[:10]  # Return first 10 behaviors


def generate_spec_yaml(behavior: Dict[str, Any]) -> str:
    """Generate spec.yaml for a behavior."""
    return f"""# ART Behavior: {behavior['name']}
# ID: {behavior['id']}
# Description: {behavior['description']}

version: "1.0"
behavior:
  id: "{behavior['id']}"
  name: "{behavior['name']}"
  description: "{behavior['description']}"
  
properties:
{chr(10).join(f"  - {prop}" for prop in behavior['properties'])}

actions:
{chr(10).join(f"  - {action}" for action in behavior['actions'])}

constraints:
  budget_limit: 300
  spam_limit: 100
  privacy_epsilon: 1.0
  capability_model: "strict"

proofs:
  - budget_ok
  - privacy_ok
  - capability_ok
  - composition_ok
"""


def generate_spec_lean(behavior: Dict[str, Any]) -> str:
    """Generate Spec.lean for a behavior."""
    return f"""/-
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

namespace ART.{behavior['id'].replace('_', '')}

open Fabric
open Fabric.Capability
open Fabric.Redaction
open Fabric.Privacy
open Fabric.Sandbox

/-- ART Behavior: {behavior['name']} -/
/-- Description: {behavior['description']} -/

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

end ART.{behavior['id'].replace('_', '')}
"""


def create_behavior_bundle(behavior: Dict[str, Any], bundles_dir: Path) -> None:
    """Create a complete behavior bundle."""
    behavior_dir = bundles_dir / "art" / behavior["id"]
    behavior_dir.mkdir(parents=True, exist_ok=True)

    # Create spec.yaml
    spec_yaml = generate_spec_yaml(behavior)
    (behavior_dir / "spec.yaml").write_text(spec_yaml, encoding="utf-8")

    # Create proofs directory and Spec.lean
    proofs_dir = behavior_dir / "proofs"
    proofs_dir.mkdir(exist_ok=True)

    spec_lean = generate_spec_lean(behavior)
    (proofs_dir / "Spec.lean").write_text(spec_lean, encoding="utf-8")

    # Copy lakefile.lean and lean-toolchain
    lakefile_content = """import Lake
open Lake DSL

package ART {
  -- add package configuration options here
}

@[default_target]
lean_lib Spec {
  -- add library configuration options here
}

require mathlib from "../../../../vendor/mathlib"
"""
    (proofs_dir / "lakefile.lean").write_text(lakefile_content, encoding="utf-8")

    lean_toolchain_content = """leanprover/lean4:v4.7.0
"""
    (proofs_dir / "lean-toolchain").write_text(lean_toolchain_content, encoding="utf-8")

    print(f"✅ Created bundle for {behavior['name']}")


def main():
    """Main function to fetch and create ART behavior bundles."""
    print("🎯 ART Benchmark Scaffolding")
    print("=" * 40)

    # Fetch behaviors
    behaviors = fetch_art_behaviors()
    print(f"📦 Found {len(behaviors)} behaviors")

    # Create bundles directory
    bundles_dir = Path("bundles")
    art_dir = bundles_dir / "art"
    art_dir.mkdir(parents=True, exist_ok=True)

    # Create bundles for each behavior
    for behavior in behaviors:
        create_behavior_bundle(behavior, bundles_dir)

    print(f"\n🎉 Created {len(behaviors)} ART behavior bundles in {art_dir}")
    print("\n📋 Next steps:")
    print("  1. Run smoke tests: python scripts/art_runner.py")
    print("  2. Verify proofs: lake build bundles/art/*/proofs")
    print("  3. Add to CI pipeline")


if __name__ == "__main__":
    main()
