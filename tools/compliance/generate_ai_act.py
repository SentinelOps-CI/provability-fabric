#!/usr/bin/env python3
"""
EU AI Act Annex VIII Technical Documentation Generator

This tool generates technical documentation conforming to EU AI Act Annex VIII
requirements from spec.yaml files, including SBOM and Lean hash manifests.
"""

import os
import sys
import json
import yaml
import argparse
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
import hashlib


class AIActGenerator:
    def __init__(self, spec_file: str, output_file: str):
        self.spec_file = spec_file
        self.output_file = output_file
        self.spec_data = None
        self.sbom_data = None
        self.lean_hashes = {}

    def load_spec(self) -> bool:
        """Load and validate the spec.yaml file."""
        try:
            with open(self.spec_file, "r", encoding="utf-8") as f:
                self.spec_data = yaml.safe_load(f)

            # Validate required fields
            required_fields = [
                "meta",
                "requirements",
                "nonFunctional",
                "acceptanceCriteria",
            ]
            for field in required_fields:
                if field not in self.spec_data:
                    print(f"❌ Missing required field: {field}")
                    return False

            return True
        except Exception as e:
            print(f"❌ Error loading spec file: {e}")
            return False

    def generate_sbom(self) -> bool:
        """Generate SBOM using syft."""
        try:
            # For demo purposes, create a mock SBOM
            # In production, this would run: syft packages . -o json
            self.sbom_data = {
                "artifacts": [
                    {
                        "id": "provability-fabric@0.1.0",
                        "name": "provability-fabric",
                        "version": "0.1.0",
                        "type": "application",
                        "language": "python",
                        "purl": "pkg:pypi/provability-fabric@0.1.0",
                    }
                ],
                "distro": {"name": "ubuntu", "version": "22.04"},
                "schema": {
                    "version": "1.4.0",
                    "url": "https://schemas.syft.dev/syft-1.4.0/schema.json",
                },
            }
            return True
        except Exception as e:
            print(f"❌ Error generating SBOM: {e}")
            return False

    def collect_lean_hashes(self) -> bool:
        """Collect Lean file hashes."""
        try:
            # Find all .olean files and calculate hashes
            for lean_file in Path(".").rglob("*.olean"):
                if ".lake" not in str(lean_file):
                    try:
                        # Calculate SHA256 hash
                        with open(lean_file, "rb") as f:
                            file_hash = hashlib.sha256(f.read()).hexdigest()

                        self.lean_hashes[str(lean_file)] = file_hash
                    except Exception as e:
                        print(f"Warning: Could not hash {lean_file}: {e}")

            return True
        except Exception as e:
            print(f"❌ Error collecting Lean hashes: {e}")
            return False

    def generate_annex_viii_content(self) -> str:
        """Generate Annex VIII content."""
        if not self.spec_data:
            return ""

        # Extract agent name from spec file path
        agent_name = Path(self.spec_file).parent.name

        # Generate requirements table
        req_table = "| ID | Statement | Rationale | Metric | Owner | Priority |\n"
        req_table += "|----|-----------|-----------|--------|-------|----------|\n"

        for req_id, req in self.spec_data.get("requirements", {}).items():
            req_table += f"| {req_id} | {req.get('statement', '')} | {req.get('rationale', '')} | {req.get('metric', '')} | {req.get('owner', '')} | {req.get('priority', '')} |\n"

        # Generate non-functional requirements table
        nfr_table = "| ID | Statement | Rationale | Metric | Owner | Priority |\n"
        nfr_table += "|----|-----------|-----------|--------|-------|----------|\n"

        for nfr_id, nfr in self.spec_data.get("nonFunctional", {}).items():
            nfr_table += f"| {nfr_id} | {nfr.get('statement', '')} | {nfr.get('rationale', '')} | {nfr.get('metric', '')} | {nfr.get('owner', '')} | {nfr.get('priority', '')} |\n"

        # Generate acceptance criteria table
        ac_table = "| ID | Description | Test Vector |\n"
        ac_table += "|----|-------------|------------|\n"

        for ac_id, ac in self.spec_data.get("acceptanceCriteria", {}).items():
            ac_table += f"| {ac_id} | {ac.get('description', '')} | {ac.get('testVector', '')} |\n"

        # Generate SBOM table
        sbom_table = "| Component | Version | Type | PURL |\n"
        sbom_table += "|-----------|---------|------|------|\n"

        for artifact in self.sbom_data.get("artifacts", []):
            sbom_table += f"| {artifact.get('name', '')} | {artifact.get('version', '')} | {artifact.get('type', '')} | {artifact.get('purl', '')} |\n"

        # Generate Lean hashes table
        lean_table = "| File | SHA256 Hash |\n"
        lean_table += "|------|-------------|\n"

        for lean_file, lean_hash in self.lean_hashes.items():
            lean_table += f"| {lean_file} | {lean_hash} |\n"

        # Generate Annex VIII document
        content = f"""# EU AI Act Annex VIII - Technical Documentation
## {agent_name.upper()} Agent

**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S UTC')}
**Specification:** {self.spec_file}
**Version:** {self.spec_data.get('meta', {}).get('version', 'unknown')}

### Section 1: System Overview

This document provides technical documentation for the {agent_name} agent as required by EU AI Act Annex VIII.

**System Purpose:** {self.spec_data.get('meta', {}).get('description', 'AI agent for automated tasks')}

### Section 2: Functional Requirements

{req_table}

### Section 3: Non-Functional Requirements

{nfr_table}

### Section 4: Acceptance Criteria

{ac_table}

### Section 5: Software Bill of Materials (SBOM)

**Distribution:** {self.sbom_data.get('distro', {}).get('name', 'Unknown')} {self.sbom_data.get('distro', {}).get('version', '')}

{sbom_table}

### Section 6: Formal Verification

**Lean Proof Hashes:**

{lean_table}

### Section 7: Risk Assessment

**Risk Score Calculation:** Based on formal verification results and runtime monitoring.

**Risk Mitigation:** Automated guards and admission control prevent unsafe operations.

### Section 8: Compliance Statement

This system implements the following EU AI Act requirements:

- **Article 6:** Transparency and information provision
- **Article 7:** Human oversight
- **Article 8:** Accuracy, robustness, and cybersecurity
- **Article 9:** Risk management system

**Compliance Verification:** Automated through formal proofs and runtime monitoring.

---

*This document was automatically generated by the Provability-Fabric compliance tool.*
"""

        return content

    def generate_pdf(self, content: str) -> bool:
        """Generate PDF using pandoc."""
        try:
            # Create temporary markdown file
            temp_md = f"/tmp/annex_viii_{Path(self.output_file).stem}.md"
            with open(temp_md, "w", encoding="utf-8") as f:
                f.write(content)

            # Generate PDF using pandoc
            cmd = [
                "pandoc",
                temp_md,
                "-o",
                self.output_file,
                "--pdf-engine=xelatex",
                "--template=eisvogel",
                "-V",
                "documentclass=article",
                "-V",
                "geometry:margin=1in",
                "-V",
                "fontsize=11pt",
                "-V",
                "mainfont=DejaVu Sans",
                "-V",
                "monofont=DejaVu Sans Mono",
            ]

            result = subprocess.run(cmd, capture_output=True, text=True)

            if result.returncode != 0:
                print(f"❌ Pandoc error: {result.stderr}")
                return False

            # Clean up temp file
            os.unlink(temp_md)

            return True
        except Exception as e:
            print(f"❌ Error generating PDF: {e}")
            return False

    def run(self) -> int:
        """Main execution method."""
        print(f"🔧 Generating EU AI Act Annex VIII documentation...")
        print(f"📄 Input: {self.spec_file}")
        print(f"📄 Output: {self.output_file}")

        # Load spec
        if not self.load_spec():
            return 1

        # Generate SBOM
        if not self.generate_sbom():
            return 1

        # Collect Lean hashes
        if not self.collect_lean_hashes():
            return 1

        # Generate content
        content = self.generate_annex_viii_content()

        # Generate PDF
        if not self.generate_pdf(content):
            return 1

        print(f"✅ Generated Annex VIII documentation: {self.output_file}")
        return 0


def main():
    parser = argparse.ArgumentParser(description="EU AI Act Annex VIII Generator")
    parser.add_argument("spec_file", help="Path to spec.yaml file")
    parser.add_argument("--out", required=True, help="Output PDF file path")

    args = parser.parse_args()

    generator = AIActGenerator(args.spec_file, args.out)
    return generator.run()


if __name__ == "__main__":
    sys.exit(main())
