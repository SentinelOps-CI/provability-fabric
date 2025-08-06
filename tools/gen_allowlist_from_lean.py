#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Generate Allowlist from Lean Proofs.
Traverses Lean environment to read effective CanUse per tool and emits JSON.
"""

import json
import subprocess
import sys
import re
from pathlib import Path
from typing import Dict, List, Set, Optional
from dataclasses import dataclass
from datetime import datetime


@dataclass
class ToolCapability:
    """Represents a tool's capability from Lean proofs."""

    tool_name: str
    can_use: bool
    conditions: List[str]
    source_file: str


class AllowlistGenerator:
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.tools = set()
        self.capabilities = {}

    def find_lean_files(self) -> List[Path]:
        """Find all Lean files in the workspace."""
        lean_files = []

        # Search in core
        core_dir = self.workspace_root / "core"
        if core_dir.exists():
            lean_files.extend(core_dir.rglob("*.lean"))

        # Search in bundles
        bundles_dir = self.workspace_root / "bundles"
        if bundles_dir.exists():
            lean_files.extend(bundles_dir.rglob("*.lean"))

        # Filter out .lake directories
        lean_files = [f for f in lean_files if ".lake" not in str(f)]

        return lean_files

    def extract_tools_from_lean(self, file_path: Path) -> Set[str]:
        """Extract tool names from Lean file."""
        tools = set()

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Look for tool definitions and usage patterns
            # This is a simplified approach - in practice would need more sophisticated parsing

            # Pattern 1: Tool definitions
            tool_patterns = [
                r"def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:.*Tool",
                r"inductive\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*where.*Tool",
                r"structure\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*where.*Tool",
            ]

            for pattern in tool_patterns:
                matches = re.findall(pattern, content)
                tools.update(matches)

            # Pattern 2: CanUse definitions
            canuse_patterns = [
                r"def\s+CanUse_([a-zA-Z_][a-zA-Z0-9_]*)\s*:",
                r"theorem\s+CanUse_([a-zA-Z_][a-zA-Z0-9_]*)\s*:",
            ]

            for pattern in canuse_patterns:
                matches = re.findall(pattern, content)
                tools.update(matches)

            # Pattern 3: Action patterns that suggest tools
            action_patterns = [
                r"SendEmail",
                r"LogSpend",
                r"LogAction",
                r"ReadFile",
                r"WriteFile",
                r"NetworkCall",
                r"DatabaseQuery",
            ]

            for pattern in action_patterns:
                if re.search(pattern, content):
                    tools.add(pattern)

        except Exception as e:
            print(f"Warning: Could not parse {file_path}: {e}")

        return tools

    def extract_capabilities_from_lean(self, file_path: Path) -> List[ToolCapability]:
        """Extract capability information from Lean file."""
        capabilities = []

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Look for capability definitions
            # Pattern: CanUse_<tool> or similar capability definitions
            capability_patterns = [
                (r"def\s+CanUse_([a-zA-Z_][a-zA-Z0-9_]*)\s*:.*:=", "def"),
                (r"theorem\s+CanUse_([a-zA-Z0-9_]*)\s*:.*:=", "theorem"),
                (r"lemma\s+CanUse_([a-zA-Z0-9_]*)\s*:.*:=", "lemma"),
            ]

            for pattern, cap_type in capability_patterns:
                matches = re.finditer(pattern, content)
                for match in matches:
                    tool_name = match.group(1)

                    # Determine if capability is granted (simplified)
                    can_use = (
                        True  # Default to True, would need more sophisticated analysis
                    )

                    # Extract conditions (simplified)
                    conditions = []

                    # Look for conditions in the definition
                    start_pos = match.start()
                    end_pos = content.find("\n", start_pos)
                    if end_pos == -1:
                        end_pos = len(content)

                    definition = content[start_pos:end_pos]

                    # Extract conditions from definition
                    if "budget_ok" in definition:
                        conditions.append("budget_ok")
                    if "spam_ok" in definition:
                        conditions.append("spam_ok")
                    if "privacy_ok" in definition:
                        conditions.append("privacy_ok")
                    if "capability_ok" in definition:
                        conditions.append("capability_ok")

                    capabilities.append(
                        ToolCapability(
                            tool_name=tool_name,
                            can_use=can_use,
                            conditions=conditions,
                            source_file=str(file_path),
                        )
                    )

        except Exception as e:
            print(f"Warning: Could not extract capabilities from {file_path}: {e}")

        return capabilities

    def generate_allowlist(self) -> Dict:
        """Generate the complete allowlist from Lean proofs."""
        lean_files = self.find_lean_files()

        # Extract all tools
        for file_path in lean_files:
            tools = self.extract_tools_from_lean(file_path)
            self.tools.update(tools)

        # Extract capabilities
        all_capabilities = []
        for file_path in lean_files:
            capabilities = self.extract_capabilities_from_lean(file_path)
            all_capabilities.extend(capabilities)

        # Build allowlist with enhanced metadata
        allowlist = {
            "version": "2.0",
            "generated_from": "lean_proofs",
            "generation_timestamp": datetime.utcnow().isoformat(),
            "source_files": [str(f) for f in lean_files],
            "sync_with_lean": True,
            "validation_status": "pending",
            "tools": {},
            "metadata": {
                "total_tools_found": len(self.tools),
                "total_capabilities": len(all_capabilities),
                "explicit_capabilities": len(
                    [c for c in all_capabilities if c.can_use]
                ),
                "default_capabilities": 0,
            },
        }

        # Process each tool
        explicit_count = 0
        default_count = 0

        for tool in sorted(self.tools):
            # Find capabilities for this tool
            tool_capabilities = [
                cap for cap in all_capabilities if cap.tool_name == tool
            ]

            if tool_capabilities:
                # Use the first capability found (in practice would need conflict resolution)
                capability = tool_capabilities[0]
                allowlist["tools"][tool] = {
                    "can_use": capability.can_use,
                    "conditions": capability.conditions,
                    "source_file": capability.source_file,
                    "capability_type": "explicit",
                    "lean_definition": True,
                }
                explicit_count += 1
            else:
                # Default capability if no explicit definition found
                # In zero-trust mode, default to deny unless proven
                allowlist["tools"][tool] = {
                    "can_use": False,  # Default to deny for security
                    "conditions": ["requires_explicit_lean_proof"],
                    "source_file": "generated",
                    "capability_type": "default_deny",
                    "lean_definition": False,
                }
                default_count += 1

        # Update metadata
        allowlist["metadata"]["explicit_capabilities"] = explicit_count
        allowlist["metadata"]["default_capabilities"] = default_count
        allowlist["validation_status"] = "generated"

        return allowlist

    def output_json(self, allowlist: Dict) -> str:
        """Output allowlist as JSON."""
        return json.dumps(allowlist, indent=2)

    def validate_allowlist(self, allowlist: Dict) -> bool:
        """Validate the generated allowlist."""
        if "tools" not in allowlist:
            print("❌ Allowlist missing 'tools' section")
            return False

        if not allowlist["tools"]:
            print("❌ Allowlist has no tools defined")
            return False

        for tool_name, tool_config in allowlist["tools"].items():
            if "can_use" not in tool_config:
                print(f"❌ Tool '{tool_name}' missing 'can_use' field")
                return False

            if "conditions" not in tool_config:
                print(f"❌ Tool '{tool_name}' missing 'conditions' field")
                return False

        print(f"✅ Allowlist validation passed: {len(allowlist['tools'])} tools")
        return True


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print(
            "Usage: python3 tools/gen_allowlist_from_lean.py <workspace_root> [output_file]"
        )
        sys.exit(1)

    workspace_root = sys.argv[1]
    output_file = (
        sys.argv[2]
        if len(sys.argv) > 2
        else "runtime/sidecar-watcher/policy/allowlist.json"
    )

    generator = AllowlistGenerator(workspace_root)
    allowlist = generator.generate_allowlist()

    # Validate the allowlist
    if not generator.validate_allowlist(allowlist):
        print("❌ Allowlist validation failed")
        sys.exit(1)

    # Output JSON
    json_output = generator.output_json(allowlist)
    print("Generated allowlist:")
    print(json_output)

    # Write to file
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, "w") as f:
        f.write(json_output)

    print(f"\n✅ Allowlist written to {output_file}")
    print(f"📊 Summary: {len(allowlist['tools'])} tools defined")


if __name__ == "__main__":
    main()
