#!/usr/bin/env python3
"""
Infrastructure Fix Script for Provability-Fabric
"""

import shutil
import subprocess
import sys
from pathlib import Path


def create_missing_directories():
    """Create missing template and bundle directories"""
    print("Creating missing directories...")

    # Create spec-templates/v1 directory
    spec_templates_dir = Path("spec-templates/v1")
    if not spec_templates_dir.exists():
        spec_templates_dir.mkdir(parents=True, exist_ok=True)

        # Create a basic template file
        template_content = """# Basic Agent Specification Template
name: "basic-agent"
version: "1.0.0"
description: "Basic agent specification"

actions:
  - name: "send_email"
    type: "email"
    budget: 100
    
  - name: "log_spend"
    type: "logging"
    budget: 50

constraints:
  - type: "budget"
    max_total: 1000
    
  - type: "rate_limit"
    action: "send_email"
    max_per_hour: 10
"""

        with open(spec_templates_dir / "basic.yaml", "w") as f:
            f.write(template_content)
        print("✅ Created basic.yaml template")
    else:
        print("✅ spec-templates/v1 already exists")

    # Create test bundle directory
    test_bundle_dir = Path("bundles/test-bundle")
    if not test_bundle_dir.exists():
        test_bundle_dir.mkdir(parents=True, exist_ok=True)

        # Copy template to test bundle
        if (spec_templates_dir / "basic.yaml").exists():
            shutil.copy(
                spec_templates_dir / "basic.yaml", test_bundle_dir / "spec.yaml"
            )
            print("✅ Created test-bundle with spec.yaml")
    else:
        print("✅ bundles/test-bundle already exists")


def check_toolchains():
    """Check toolchain status"""
    print("\nChecking toolchains...")

    # Check Lean
    try:
        result = subprocess.run(
            "lake --version", shell=True, capture_output=True, text=True
        )
        if result.returncode == 0:
            print("✅ Lean/Lake is working")
        else:
            print("❌ Lean/Lake has issues")
    except:
        print("❌ Lean/Lake not found")

    # Check Rust
    try:
        result = subprocess.run(
            "cargo --version", shell=True, capture_output=True, text=True
        )
        if result.returncode == 0:
            print("✅ Rust/Cargo is working")
        else:
            print("❌ Rust/Cargo has issues")
    except:
        print("❌ Rust/Cargo not found")


def main():
    """Main function"""
    print("🚀 Provability-Fabric Infrastructure Fix")
    print("=" * 50)

    create_missing_directories()
    check_toolchains()

    print("\n📚 Next Steps:")
    print("1. Fix Rust toolchain: https://rustup.rs/")
    print("2. Start Redis: redis-server")
    print("3. Start ledger: cd runtime/ledger && npm start")
    print("4. Run tests: lake build && cargo test")

    return 0


if __name__ == "__main__":
    sys.exit(main())
