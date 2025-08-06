#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

AST-Hash Duplicate Enforcer for Lean definitions.
Detects functionally identical definitions across bundles using normalized AST
hashing.
"""

import json
import hashlib
import sys
import re
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class Definition:
    """Represents a Lean definition with its normalized AST hash."""

    module: str
    name: str
    file_path: str
    ast_hash: str
    definition_type: str  # 'def', 'theorem', 'inductive', etc.


class ASTHashEnforcer:
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.allowlist_patterns = [r"ui/", r"tests/", r"spec-templates/.*"]

    def is_allowlisted(self, file_path: str) -> bool:
        """Check if file is in allowlist (ignored for duplicate detection)."""
        for pattern in self.allowlist_patterns:
            if re.search(pattern, file_path):
                return True
        return False

    def get_lean_files(self) -> List[Path]:
        """Find all Lean files in bundles and spec-templates."""
        lean_files = []

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

    def get_lean_ast(self, file_path: Path) -> Optional[str]:
        """Get normalized content from Lean file for duplicate detection."""
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            
            # Normalize the content for duplicate detection
            return self.normalize_ast(content)
            
        except Exception as e:
            print(f"Warning: Error reading {file_path}: {e}")
            return None

    def normalize_ast(self, ast_content: str) -> str:
        """Normalize content by removing docstrings, positions, and whitespace."""
        # Remove docstrings (/- ... -/)
        ast_content = re.sub(r"/-.*?-/", "", ast_content, flags=re.DOTALL)
        
        # Remove single-line comments (-- ...)
        ast_content = re.sub(
            r"--.*$", "", ast_content, flags=re.MULTILINE
        )
        
        # Remove position information (line:column)
        ast_content = re.sub(r"\d+:\d+", "", ast_content)
        
        # Remove extra whitespace and normalize
        ast_content = re.sub(r"\s+", " ", ast_content)
        ast_content = ast_content.strip()
        
        return ast_content

    def extract_definitions_from_ast(
        self, ast_content: str, file_path: str
    ) -> List[Definition]:
        """Extract individual definitions from AST content."""
        definitions = []

        # Split by definition patterns
        def_patterns = [
            (r"def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", "def"),
            (r"theorem\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", "theorem"),
            (r"inductive\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", "inductive"),
            (r"structure\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", "structure"),
            (r"class\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", "class"),
        ]

        for pattern, def_type in def_patterns:
            matches = re.finditer(pattern, ast_content)
            for match in matches:
                def_name = match.group(1)

                # Extract the definition body (simplified approach)
                start_pos = match.start()
                body_start = ast_content.find(":", start_pos)
                if body_start != -1:
                    # Try to find the end of this definition
                    # This is a simplified approach - in practice would need
                    # proper Lean parsing
                    body_content = ast_content[body_start:]

                    # Create a hash of the normalized body
                    normalized_body = self.normalize_ast(body_content)
                    ast_hash = hashlib.sha256(normalized_body.encode()).hexdigest()

                    # Extract module name from file path
                    module = self.extract_module_name(file_path)

                    definitions.append(
                        Definition(
                            module=module,
                            name=def_name,
                            file_path=file_path,
                            ast_hash=ast_hash,
                            definition_type=def_type,
                        )
                    )

        return definitions

    def extract_module_name(self, file_path: str) -> str:
        """Extract module name from file path."""
        path = Path(file_path)

        # Handle bundles structure
        if "bundles" in str(path):
            # bundles/my-agent/proofs/Spec.lean -> my-agent.Spec
            parts = path.parts
            if len(parts) >= 3:
                bundle_name = parts[parts.index("bundles") + 1]
                file_name = path.stem
                return f"{bundle_name}.{file_name}"

        # Handle spec-templates structure
        if "spec-templates" in str(path):
            # spec-templates/v1/Spec.lean -> v1.Spec
            parts = path.parts
            if len(parts) >= 2:
                template_name = parts[parts.index("spec-templates") + 1]
                file_name = path.stem
                return f"{template_name}.{file_name}"

        return path.stem

    def find_duplicates(self) -> Dict[str, List[Definition]]:
        """Find duplicate definitions based on AST hash."""
        all_definitions = []

        # Process all Lean files
        for lean_file in self.get_lean_files():
            if self.is_allowlisted(str(lean_file)):
                continue

            ast_content = self.get_lean_ast(lean_file)
            if ast_content:
                definitions = self.extract_definitions_from_ast(
                    ast_content, str(lean_file)
                )
                all_definitions.extend(definitions)

        # Group by AST hash
        hash_groups = defaultdict(list)
        for definition in all_definitions:
            hash_groups[definition.ast_hash].append(definition)

        # Return only groups with more than one definition
        duplicates = {
            hash_val: definitions
            for hash_val, definitions in hash_groups.items()
            if len(definitions) > 1
        }

        return duplicates

    def generate_report(self, duplicates: Dict[str, List[Definition]]) -> str:
        """Generate a human-readable report of duplicates."""
        if not duplicates:
            return "✅ 0 functional duplicates found"

        report = ["❌ Functional duplicates found:"]

        for ast_hash, definitions in duplicates.items():
            report.append(f"\nHash: {ast_hash[:8]}...")
            for definition in definitions:
                report.append(
                    f"  - {definition.module}.{definition.name} ({definition.definition_type}) in {definition.file_path}"
                )

        return "\n".join(report)

    def output_json(self, duplicates: Dict[str, List[Definition]]) -> str:
        """Output duplicates in JSON format for CI consumption."""
        json_data = {}

        for ast_hash, definitions in duplicates.items():
            json_data[ast_hash] = [f"{defn.module}.{defn.name}" for defn in definitions]

        return json.dumps(json_data, indent=2)


def main():
    """Main entry point."""
    workspace_root = sys.argv[1] if len(sys.argv) > 1 else "."

    enforcer = ASTHashEnforcer(workspace_root)
    duplicates = enforcer.find_duplicates()

    # Output report
    report = enforcer.generate_report(duplicates)
    print(report)

    # Output JSON for CI
    if duplicates:
        json_output = enforcer.output_json(duplicates)
        print(f"\nJSON output:\n{json_output}")
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
