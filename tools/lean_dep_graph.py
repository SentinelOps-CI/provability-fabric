#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Lean Dependency Graph Builder.
Builds module dependency graphs by parsing import lines and Lake manifest.
"""

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Set, Optional
from dataclasses import dataclass
from collections import defaultdict, deque


@dataclass
class Module:
    """Represents a Lean module with its dependencies."""

    name: str
    file_path: str
    dependencies: Set[str]
    is_bundle: bool = False


class LeanDepGraph:
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.modules: Dict[str, Module] = {}
        self.reverse_deps: Dict[str, Set[str]] = defaultdict(set)

    def parse_lake_manifest(self) -> Dict[str, str]:
        """Parse lake-manifest.json to get module paths."""
        manifest_path = self.workspace_root / "lake-manifest.json"
        if not manifest_path.exists():
            return {}

        try:
            with open(manifest_path, "r") as f:
                manifest = json.load(f)

            # Extract module information from manifest
            module_paths = {}
            for entry in manifest.get("packages", []):
                name = entry.get("name", "")
                path = entry.get("path", "")
                if name and path:
                    module_paths[name] = str(self.workspace_root / path)

            return module_paths
        except Exception as e:
            print(f"Warning: Could not parse lake-manifest.json: {e}")
            return {}

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

        # Search in spec-templates
        spec_templates_dir = self.workspace_root / "spec-templates"
        if spec_templates_dir.exists():
            lean_files.extend(spec_templates_dir.rglob("*.lean"))

        # Filter out .lake directories
        lean_files = [f for f in lean_files if ".lake" not in str(f)]

        return lean_files

    def extract_module_name(self, file_path: Path) -> str:
        """Extract module name from file path."""
        # Handle bundles structure
        if "bundles" in str(file_path):
            # bundles/my-agent/proofs/Spec.lean -> my-agent.Spec
            parts = file_path.parts
            if len(parts) >= 3:
                bundle_name = parts[parts.index("bundles") + 1]
                file_name = file_path.stem
                return f"{bundle_name}.{file_name}"

        # Handle spec-templates structure
        if "spec-templates" in str(file_path):
            # spec-templates/v1/Spec.lean -> v1.Spec
            parts = file_path.parts
            if len(parts) >= 2:
                template_name = parts[parts.index("spec-templates") + 1]
                file_name = file_path.stem
                return f"{template_name}.{file_name}"

        # Handle core structure
        if "core" in str(file_path):
            # core/lean-libs/ActionDSL.lean -> Fabric.ActionDSL
            parts = file_path.parts
            if len(parts) >= 3:
                lib_name = parts[parts.index("lean-libs") + 1]
                return f"Fabric.{lib_name}"

        return file_path.stem

    def parse_imports(self, file_path: Path) -> Set[str]:
        """Parse import statements from a Lean file."""
        imports = set()

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Find import statements
            import_pattern = r"import\s+([a-zA-Z_][a-zA-Z0-9_.]*)"
            matches = re.findall(import_pattern, content)

            for match in matches:
                # Handle qualified imports (e.g., "Fabric.ActionDSL")
                if "." in match:
                    imports.add(match)
                else:
                    imports.add(match)

        except Exception as e:
            print(f"Warning: Could not parse imports from {file_path}: {e}")

        return imports

    def build_dependency_graph(self):
        """Build the complete dependency graph."""
        lean_files = self.find_lean_files()

        # First pass: create module objects
        for file_path in lean_files:
            module_name = self.extract_module_name(file_path)
            dependencies = self.parse_imports(file_path)
            is_bundle = "bundles" in str(file_path)

            self.modules[module_name] = Module(
                name=module_name,
                file_path=str(file_path),
                dependencies=dependencies,
                is_bundle=is_bundle,
            )

        # Second pass: build reverse dependency graph
        for module_name, module in self.modules.items():
            for dep in module.dependencies:
                self.reverse_deps[dep].add(module_name)

    def get_impacted_modules(self, changed_files: List[str]) -> Set[str]:
        """Get all modules that are impacted by changes to the given files."""
        impacted = set()
        to_process = deque()

        # Convert file paths to module names
        for file_path in changed_files:
            path = Path(file_path)
            module_name = self.extract_module_name(path)
            if module_name in self.modules:
                to_process.append(module_name)
                impacted.add(module_name)

        # BFS to find all impacted modules
        while to_process:
            module_name = to_process.popleft()

            # Add all modules that depend on this module
            for dependent in self.reverse_deps.get(module_name, []):
                if dependent not in impacted:
                    impacted.add(dependent)
                    to_process.append(dependent)

        return impacted

    def get_build_targets(self, impacted_modules: Set[str]) -> List[str]:
        """Convert impacted modules to Lake build targets."""
        targets = []

        for module_name in impacted_modules:
            module = self.modules.get(module_name)
            if module:
                # Convert module name to Lake target
                if module.is_bundle:
                    # Bundle targets: bundles/my-agent/proofs
                    bundle_path = Path(module.file_path).parent
                    target = str(bundle_path.relative_to(self.workspace_root))
                    targets.append(target)
                else:
                    # Core targets: core/lean-libs
                    core_path = Path(module.file_path).parent
                    target = str(core_path.relative_to(self.workspace_root))
                    targets.append(target)

        return list(set(targets))  # Remove duplicates

    def output_json(self) -> str:
        """Output dependency graph as JSON."""
        graph_data = {"modules": {}, "reverse_deps": {}}

        for module_name, module in self.modules.items():
            graph_data["modules"][module_name] = {
                "file_path": module.file_path,
                "dependencies": list(module.dependencies),
                "is_bundle": module.is_bundle,
            }

        for dep, dependents in self.reverse_deps.items():
            graph_data["reverse_deps"][dep] = list(dependents)

        return json.dumps(graph_data, indent=2)


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print(
            "Usage: python3 tools/lean_dep_graph.py <workspace_root> [changed_files...]"
        )
        sys.exit(1)

    workspace_root = sys.argv[1]
    changed_files = sys.argv[2:] if len(sys.argv) > 2 else []

    dep_graph = LeanDepGraph(workspace_root)
    dep_graph.build_dependency_graph()

    if changed_files:
        # Get impacted modules
        impacted_modules = dep_graph.get_impacted_modules(changed_files)
        build_targets = dep_graph.get_build_targets(impacted_modules)

        # Output for CI consumption
        print("Impacted modules:")
        for module in sorted(impacted_modules):
            print(f"  - {module}")

        print("\nBuild targets:")
        for target in sorted(build_targets):
            print(f"  - {target}")

        # Output as JSON for further processing
        result = {
            "impacted_modules": list(impacted_modules),
            "build_targets": build_targets,
        }
        print(f"\nJSON output:\n{json.dumps(result, indent=2)}")
    else:
        # Output full dependency graph
        print(dep_graph.output_json())


if __name__ == "__main__":
    main()
