#!/usr/bin/env python3
"""
ART to Bundle Converter

Converts ART dataset entries into Provability-Fabric bundle specifications.
Creates spec.yaml and proofs/Spec.lean for each behavior category.
"""

import json
import sys
from pathlib import Path
from typing import Dict, List

import click


class ARTBundleConverter:
    """Converts ART dataset entries to Provability-Fabric bundles."""

    def __init__(self, dataset_path: Path, output_dir: Path):
        self.dataset_path = dataset_path
        self.output_dir = output_dir
        self.behaviors: Dict[str, List[Dict]] = {}

    def load_dataset(self) -> bool:
        """Load and parse ART dataset."""
        try:
            print(f"Loading dataset from {self.dataset_path}")

            with open(self.dataset_path, "r") as f:
                for line_num, line in enumerate(f, 1):
                    try:
                        entry = json.loads(line.strip())
                        behavior = entry.get("behavior", "unknown")

                        if behavior not in self.behaviors:
                            self.behaviors[behavior] = []

                        self.behaviors[behavior].append(entry)

                    except json.JSONDecodeError as e:
                        print(f"Warning: Invalid JSON on line {line_num}: {e}")
                        continue

            print(f"Loaded {len(self.behaviors)} behavior categories")
            for behavior, entries in self.behaviors.items():
                print(f"  {behavior}: {len(entries)} entries")

            return True

        except Exception as e:
            print(f"Error loading dataset: {e}")
            return False

    def generate_spec_yaml(self, behavior: str, entries: List[Dict]) -> str:
        """Generate spec.yaml content for a behavior category."""

        # Extract common patterns from entries
        tools_used = set()
        system_prompts = set()

        for entry in entries:
            if "tools" in entry:
                for tool in entry["tools"]:
                    tools_used.add(tool.get("name", "unknown"))

            if "system_prompt" in entry:
                system_prompts.add(entry["system_prompt"])

        # Create tool schema
        tool_schema = {"type": "object", "properties": {}, "required": []}

        for tool_name in tools_used:
            tool_schema["properties"][tool_name] = {
                "type": "object",
                "properties": {
                    "parameters": {"type": "object"},
                    "description": {"type": "string"},
                },
            }

        # Create policy based on behavior
        policy = self._generate_policy_for_behavior(behavior, entries)

        # Generate spec.yaml
        spec_content = f"""# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# ART Behavior: {behavior}

meta:
  version: "0.1.0"
  created: "2025-01-15T00:00:00Z"
  status: "draft"
  title: "ART {behavior} Agent Specification"
  description: "Provability-Fabric specification for ART {behavior} behavior"

requirements:
  REQ-0001:
    statement: "The agent SHALL validate all inputs against JSON schema before processing"
    rationale: "Prevent injection attacks and ensure data integrity"
    metric: "100% input validation rate"
    owner: "Security Officer"
    priority: "high"
    category: "security"
    
  REQ-0002:
    statement: "The agent SHALL enforce tool-level invariants and access controls"
    rationale: "Prevent unauthorized tool usage and policy violations"
    metric: "Zero tool policy violations"
    owner: "Security Officer"
    priority: "high"
    category: "security"
    
  REQ-0003:
    statement: "The agent SHALL maintain budget limits and resource constraints"
    rationale: "Prevent resource abuse and maintain service quality"
    metric: "Zero budget violations"
    owner: "System Architect"
    priority: "high"
    category: "resource-management"

nonFunctional:
  NFR-0001:
    statement: "Agent response time shall not exceed 20ms for 95% of requests"
    rationale: "Ensure responsive user experience for ART benchmark"
    metric: "P95 latency ≤ 20ms"
    owner: "Operations Lead"
    priority: "high"
    category: "performance"
    
  NFR-0002:
    statement: "Agent shall block 99% of malicious attempts in ART benchmark"
    rationale: "Demonstrate effectiveness against red team attacks"
    metric: "Block rate ≥ 99%"
    owner: "Security Officer"
    priority: "high"
    category: "security"

acceptanceCriteria:
  AC-0001:
    description: "All agent inputs are validated against JSON schema with 100% coverage"
    testProcedure: "Execute ART test suite and verify all inputs are validated"
    successCriteria: "Zero invalid inputs accepted"
    
  AC-0002:
    description: "Tool-level invariants are enforced with zero violations"
    testProcedure: "Execute ART attacks and verify tool policy enforcement"
    successCriteria: "Zero tool policy violations allowed"
    
  AC-0003:
    description: "Budget limits are enforced with zero violations during testing"
    testProcedure: "Execute ART attacks and verify budget enforcement"
    successCriteria: "Zero budget violations allowed"
    
  AC-0004:
    description: "Agent responds within 20ms for 95% of ART test requests"
    testProcedure: "Execute ART benchmark and measure response times"
    successCriteria: "P95 response time ≤ 20ms"

trace:
  REQ-0001: ["AC-0001"]
  REQ-0002: ["AC-0002"]
  REQ-0003: ["AC-0003"]
  NFR-0001: ["AC-0004"]
  NFR-0002: ["AC-0002"]

# ART-specific configuration
art:
  behavior: "{behavior}"
  entry_count: {len(entries)}
  tools_used: {list(tools_used)}
  system_prompts: {list(system_prompts)}
  policy: {json.dumps(policy, indent=2)}
"""

        return spec_content

    def _generate_policy_for_behavior(self, behavior: str, entries: List[Dict]) -> Dict:
        """Generate policy rules based on behavior category."""

        # Base policy for all behaviors
        policy = {
            "budget_limit": 100.0,
            "spam_score_limit": 0.8,
            "tool_access": {},
            "privacy_epsilon": 1.0,
            "privacy_delta": 1e-5,
        }

        # Behavior-specific policies
        if "confidentiality" in behavior.lower():
            policy.update(
                {
                    "no_pii_egress": True,
                    "encryption_required": True,
                    "audit_logging": True,
                }
            )

        elif "policy" in behavior.lower():
            policy.update(
                {
                    "role_based_access": True,
                    "action_approval": True,
                    "compliance_checking": True,
                }
            )

        elif "override" in behavior.lower():
            policy.update(
                {
                    "safety_checks": True,
                    "confirmation_required": True,
                    "rate_limiting": True,
                }
            )

        elif "budget" in behavior.lower():
            policy.update(
                {"budget_limit": 50.0, "cost_tracking": True, "spending_alerts": True}
            )

        return policy

    def generate_spec_lean(self, behavior: str, entries: List[Dict]) -> str:
        """Generate Spec.lean content for a behavior category."""

        # Extract tools used in this behavior
        tools_used = set()
        for entry in entries:
            if "tools" in entry:
                for tool in entry["tools"]:
                    tools_used.add(tool.get("name", "unknown"))

        # Generate Lean action types based on tools
        action_types = []
        for tool in tools_used:
            action_types.append(f"  | {tool.capitalize()} (params : String)")

        action_types_str = "\n".join(action_types) if action_types else "  | NoAction"

        # Generate Lean content
        lean_content = f"""/-
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
import Mathlib.Data.Float.Basic
import Mathlib.Algebra.Order.Ring

namespace Spec

/-- Action types for ART {behavior} behavior -/
inductive Action where
{action_types_str}

/-- Check if a list of actions respects policy constraints -/
def policy_ok : List Action → Prop
  | [] => True
  | action :: rest => sorry  -- TODO: Implement specific policy checks

/-- Check if actions respect budget constraints -/
def budget_ok : List Action → Prop
  | [] => True
  | action :: rest => sorry  -- TODO: Implement budget checking

/-- Check if actions respect privacy constraints -/
def privacy_ok : List Action → Prop
  | [] => True
  | action :: rest => sorry  -- TODO: Implement privacy checking

/-- Theorem: all action traces respect policy constraints -/
theorem thm_policy_ok : ∀ (tr : List Action), policy_ok tr := by
  sorry  -- TODO: Implement proof

/-- Theorem: all action traces respect budget constraints -/
theorem thm_budget_ok : ∀ (tr : List Action), budget_ok tr := by
  sorry  -- TODO: Implement proof

/-- Theorem: all action traces respect privacy constraints -/
theorem thm_privacy_ok : ∀ (tr : List Action), privacy_ok tr := by
  sorry  -- TODO: Implement proof

/-- Main theorem: all action traces are safe -/
theorem thm_safe_actions : ∀ (tr : List Action), 
  policy_ok tr ∧ budget_ok tr ∧ privacy_ok tr := by
  intro tr
  constructor
  · exact thm_policy_ok tr
  · constructor
    · exact thm_budget_ok tr
    · exact thm_privacy_ok tr

end Spec
"""

        return lean_content

    def create_bundle(self, behavior: str, entries: List[Dict]) -> bool:
        """Create bundle directory and files for a behavior."""

        # Create bundle directory
        bundle_dir = self.output_dir / behavior
        bundle_dir.mkdir(parents=True, exist_ok=True)

        # Create proofs directory
        proofs_dir = bundle_dir / "proofs"
        proofs_dir.mkdir(exist_ok=True)

        try:
            # Generate spec.yaml
            spec_content = self.generate_spec_yaml(behavior, entries)
            spec_file = bundle_dir / "spec.yaml"
            with open(spec_file, "w") as f:
                f.write(spec_content)

            # Generate Spec.lean
            lean_content = self.generate_spec_lean(behavior, entries)
            lean_file = proofs_dir / "Spec.lean"
            with open(lean_file, "w") as f:
                f.write(lean_content)

            # Generate lakefile.lean
            lakefile_content = """import Lake
open Lake DSL

package spec {
  -- add package configuration options here
}

@[default_target]
lean_lib Spec {
  -- add library configuration options here
}
"""
            lakefile_file = proofs_dir / "lakefile.lean"
            with open(lakefile_file, "w") as f:
                f.write(lakefile_content)

            print(f"✓ Created bundle for {behavior}")
            return True

        except Exception as e:
            print(f"Error creating bundle for {behavior}: {e}")
            return False

    def convert_all(self) -> bool:
        """Convert all behaviors to bundles."""

        if not self.load_dataset():
            return False

        success_count = 0
        total_count = len(self.behaviors)

        for behavior, entries in self.behaviors.items():
            if self.create_bundle(behavior, entries):
                success_count += 1

        print(f"\nConversion complete: {success_count}/{total_count} bundles created")
        return success_count == total_count


@click.command()
@click.argument("dataset_path", type=click.Path(exists=True))
@click.argument("output_dir", type=click.Path())
@click.option("--behavior", help="Convert only specific behavior")
def main(dataset_path: str, output_dir: str, behavior: str = None):
    """Convert ART dataset to Provability-Fabric bundles."""

    dataset_path = Path(dataset_path)
    output_dir = Path(output_dir)

    converter = ARTBundleConverter(dataset_path, output_dir)

    if behavior:
        # Convert single behavior
        if not converter.load_dataset():
            sys.exit(1)

        if behavior not in converter.behaviors:
            print(f"Behavior '{behavior}' not found in dataset")
            sys.exit(1)

        entries = converter.behaviors[behavior]
        if converter.create_bundle(behavior, entries):
            print("✓ Single behavior conversion successful")
            sys.exit(0)
        else:
            print("✗ Single behavior conversion failed")
            sys.exit(1)
    else:
        # Convert all behaviors
        if converter.convert_all():
            print("✓ All behaviors converted successfully")
            sys.exit(0)
        else:
            print("✗ Some behaviors failed to convert")
            sys.exit(1)


if __name__ == "__main__":
    main()
