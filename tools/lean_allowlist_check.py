#!/usr/bin/env python3
"""
Cross-check Lean allow-list definitions against runtime JSON configuration.

This script ensures that the formal Lean definitions in
core/lean-libs/Capability.lean match the runtime configuration in
runtime/sidecar-watcher/policy/allowlist.json.
"""

import json
import re
import sys
from pathlib import Path
from typing import Dict, Set


def parse_lean_capability_definitions(lean_file: Path) -> Dict[str, Set[str]]:
    """Parse Lean file to extract agent capability definitions."""
    if not lean_file.exists():
        print(f"Error: Lean file {lean_file} not found")
        return {}

    content = lean_file.read_text()

    # Extract agent_can_use_tool definitions
    # Pattern: def agent_can_use_tool (agent_id : String) (tool : Tool) : Prop :=
    #         match agent_id with
    #         | "agent-name" => tool = Tool.SendEmail ∨ tool = Tool.LogSpend ∨ ...
    
    # Find the agent_can_use_tool definition
    agent_pattern = (
        r'def\s+agent_can_use_tool.*?match\s+agent_id\s+with(.*?)(?=\n\s*end|$)'
    )
    match = re.search(agent_pattern, content, re.MULTILINE | re.DOTALL)
    
    if not match:
        print("❌ Could not find agent_can_use_tool definition in Lean file")
        return {}

    match_content = match.group(1)
    
    # Extract individual agent patterns
    agent_cases = re.findall(
        r'\|\s*"([^"]+)"\s*=>\s*(.+?)(?=\n\s*\||\n\s*end|$)',
        match_content, re.MULTILINE | re.DOTALL
    )
    
    agents = {}
    for agent_id, tool_conditions in agent_cases:
        tools = set()
        
        # Parse tool conditions
        if "Tool.SendEmail" in tool_conditions:
            tools.add("SendEmail")
        if "Tool.LogSpend" in tool_conditions:
            tools.add("LogSpend")
        if "Tool.LogAction" in tool_conditions:
            tools.add("LogAction")
        if "Tool.NetworkCall" in tool_conditions:
            tools.add("NetworkCall")
        if "Tool.FileRead" in tool_conditions:
            tools.add("FileRead")
        if "Tool.FileWrite" in tool_conditions:
            tools.add("FileWrite")
        
        agents[agent_id] = tools

    return agents


def parse_runtime_allowlist(json_file: Path) -> Dict[str, Set[str]]:
    """Parse runtime JSON allow-list configuration."""
    if not json_file.exists():
        print(f"Error: JSON file {json_file} not found")
        return {}

    with open(json_file) as f:
        config = json.load(f)

    agents = {}
    for agent_id, agent_config in config.get("agents", {}).items():
        allowed_tools = set(agent_config.get("allowed_tools", []))
        agents[agent_id] = allowed_tools

    return agents


def compare_definitions(
    lean_agents: Dict[str, Set[str]], json_agents: Dict[str, Set[str]]
) -> bool:
    """Compare Lean and JSON definitions for consistency."""
    all_agents = set(lean_agents.keys()) | set(json_agents.keys())

    differences = []

    for agent_id in all_agents:
        lean_tools = lean_agents.get(agent_id, set())
        json_tools = json_agents.get(agent_id, set())

        if lean_tools != json_tools:
            missing_in_json = lean_tools - json_tools
            missing_in_lean = json_tools - lean_tools

            if missing_in_json or missing_in_lean:
                differences.append(
                    {
                        "agent": agent_id,
                        "lean_tools": sorted(lean_tools),
                        "json_tools": sorted(json_tools),
                        "missing_in_json": sorted(missing_in_json),
                        "missing_in_lean": sorted(missing_in_lean),
                    }
                )

    if differences:
        print("❌ Lean and JSON definitions differ:")
        for diff in differences:
            print(f"  Agent: {diff['agent']}")
            print(f"    Lean tools: {diff['lean_tools']}")
            print(f"    JSON tools: {diff['json_tools']}")
            if diff["missing_in_json"]:
                print(f"    Missing in JSON: {diff['missing_in_json']}")
            if diff["missing_in_lean"]:
                print(f"    Missing in Lean: {diff['missing_in_lean']}")
            print()
        return False
    else:
        print("✅ Lean and JSON definitions are consistent")
        return True


def main():
    """Main function to cross-check Lean and JSON definitions."""
    project_root = Path(__file__).parent.parent
    lean_file = project_root / "core" / "lean-libs" / "Capability.lean"
    json_file = (
        project_root / "runtime" / "sidecar-watcher" / "policy" / "allowlist.json"
    )

    print("🔍 Cross-checking Lean allow-list vs runtime JSON...")
    print(f"  Lean file: {lean_file}")
    print(f"  JSON file: {json_file}")
    print()

    # Parse definitions
    lean_agents = parse_lean_capability_definitions(lean_file)
    json_agents = parse_runtime_allowlist(json_file)

    if not lean_agents:
        print("❌ Failed to parse Lean definitions")
        sys.exit(1)

    if not json_agents:
        print("❌ Failed to parse JSON definitions")
        sys.exit(1)

    # Compare definitions
    is_consistent = compare_definitions(lean_agents, json_agents)

    if not is_consistent:
        print("\n💡 To fix inconsistencies:")
        print("  1. Update the Lean definitions in core/lean-libs/Capability.lean")
        print(
            "  2. Update the JSON configuration in runtime/sidecar-watcher/policy/allowlist.json"
        )
        print("  3. Ensure both files reflect the same capability model")
        sys.exit(1)

    print("\n🎉 All definitions are consistent!")


if __name__ == "__main__":
    main()
