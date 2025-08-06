#!/usr/bin/env python3
"""
Lean Proof Quality Gate

Scans Lean proofs for sorry/admit statements and enforces time-based policies.
- No sorry/admit older than 48 hours (configurable)
- Tracks timestamps and provides clear error messages
- Supports exception lists for legitimate admits
"""

import os
import sys
import yaml
import argparse
import time
from pathlib import Path
from typing import List, Dict, Tuple, Optional


class LeanGate:
    def __init__(self, config_path: Optional[str] = None):
        self.config = self._load_config(config_path)
        self.max_age_hours = self.config.get("max_age_hours", 48)
        self.exceptions = self.config.get("exceptions", [])
        self.lean_extensions = {".lean"}

    def _load_config(self, config_path: Optional[str]) -> Dict:
        """Load configuration from YAML file or use defaults."""
        if config_path and os.path.exists(config_path):
            with open(config_path, "r") as f:
                return yaml.safe_load(f)
        return {}

    def find_lean_files(self, root_dir: str) -> List[Path]:
        """Find all Lean files in the given directory."""
        lean_files = []
        for root, dirs, files in os.walk(root_dir):
            # Skip .lake directories
            dirs[:] = [d for d in dirs if d != ".lake"]

            for file in files:
                if Path(file).suffix in self.lean_extensions:
                    lean_files.append(Path(root) / file)
        return lean_files

    def scan_file_for_admits(self, file_path: Path) -> List[Tuple[int, str, str]]:
        """Scan a Lean file for sorry/admit statements and return line info."""
        admits = []
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                for line_num, line in enumerate(f, 1):
                    line = line.strip()
                    if "sorry" in line or "by admit" in line:
                        admit_type = "sorry" if "sorry" in line else "by admit"
                        admits.append((line_num, line, admit_type))
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
        return admits

    def is_file_excepted(self, file_path: Path) -> bool:
        """Check if a file is in the exceptions list."""
        file_str = str(file_path)
        for exception in self.exceptions:
            if exception in file_str:
                return True
        return False

    def get_file_age_hours(self, file_path: Path) -> float:
        """Get the age of a file in hours."""
        try:
            mtime = file_path.stat().st_mtime
            age_seconds = time.time() - mtime
            return age_seconds / 3600
        except Exception:
            return float("inf")

    def check_file(self, file_path: Path) -> Dict:
        """Check a single file for admits and age violations."""
        if self.is_file_excepted(file_path):
            return {"file": file_path, "status": "excepted", "admits": []}

        admits = self.scan_file_for_admits(file_path)
        age_hours = self.get_file_age_hours(file_path)

        # Check if any admits are too old
        old_admits = []
        for line_num, line, admit_type in admits:
            if age_hours > self.max_age_hours:
                old_admits.append(
                    {
                        "line": line_num,
                        "content": line,
                        "type": admit_type,
                        "age_hours": age_hours,
                    }
                )

        return {
            "file": file_path,
            "status": "failed" if old_admits else "passed",
            "admits": admits,
            "old_admits": old_admits,
            "age_hours": age_hours,
        }

    def run_scan(self, root_dir: str) -> List[Dict]:
        """Run the complete scan and return results."""
        print(f"🔍 Scanning Lean files in {root_dir}")
        print(f"📋 Max age: {self.max_age_hours} hours")
        print(f"📋 Exceptions: {len(self.exceptions)} patterns")

        lean_files = self.find_lean_files(root_dir)
        print(f"📁 Found {len(lean_files)} Lean files")

        results = []
        failed_files = []

        for file_path in lean_files:
            result = self.check_file(file_path)
            results.append(result)

            if result["status"] == "failed":
                failed_files.append(result)

        return results, failed_files

    def print_results(self, results: List[Dict], failed_files: List[Dict]):
        """Print scan results in a clear format."""
        print("\n" + "=" * 60)
        print("📊 LEAN PROOF QUALITY GATE RESULTS")
        print("=" * 60)

        if not failed_files:
            print("✅ All Lean files pass quality gates!")
            return True

        print(f"❌ Found {len(failed_files)} files with violations:")
        print()

        for result in failed_files:
            print(f"📄 {result['file']}")
            print(f"   Age: {result['age_hours']:.1f} hours")
            print(f"   Total admits: {len(result['admits'])}")
            print("   Old admits:")

            for admit in result["old_admits"]:
                print(f"     Line {admit['line']}: {admit['content']}")
            print()

        print("💡 To fix:")
        print("   1. Replace 'sorry' with actual proofs")
        print("   2. Replace 'by admit' with proper tactics")
        print("   3. Add files to exceptions list if legitimate")
        print("   4. Files have 48 hours to be resolved")

        return False


def main():
    parser = argparse.ArgumentParser(description="Lean Proof Quality Gate")
    parser.add_argument("--root", default=".", help="Root directory to scan")
    parser.add_argument("--config", help="Path to config YAML file")
    parser.add_argument("--max-age", type=int, default=48, help="Max age in hours")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    # Create gate instance
    gate = LeanGate(args.config)
    if args.max_age != 48:
        gate.max_age_hours = args.max_age

    # Run scan
    results, failed_files = gate.run_scan(args.root)

    # Print results
    success = gate.print_results(results, failed_files)

    # Exit with appropriate code
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
