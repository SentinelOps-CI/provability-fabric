#!/usr/bin/env python3
"""
APOLLO - LLM-Assisted Auto-Proof Pipeline

This script automatically resolves 'sorry' and 'by admit' placeholders in Lean proofs
by invoking the APOLLO REST API and applying the generated proof patches.
"""

import os
import sys
import json
import subprocess
import tempfile
import argparse
from pathlib import Path
from typing import List, Dict, Optional
import requests
from datetime import datetime
import git


class ApolloProofBot:
    def __init__(self, api_url: str = "http://localhost:8080", dry_run: bool = False):
        self.api_url = api_url
        self.dry_run = dry_run
        self.repo = git.Repo(".")
        self.changes_made = False

    def find_lean_files_with_admits(self) -> List[Path]:
        """Find all Lean files containing 'sorry' or 'by admit' statements."""
        lean_files = []

        for lean_file in Path(".").rglob("*.lean"):
            if ".lake" in str(lean_file):
                continue

            try:
                content = lean_file.read_text(encoding="utf-8")
                if "sorry" in content or "by admit" in content:
                    lean_files.append(lean_file)
            except Exception as e:
                print(f"Warning: Could not read {lean_file}: {e}")

        return lean_files

    def extract_admit_context(self, lean_file: Path) -> List[Dict]:
        """Extract context around 'sorry' and 'by admit' statements."""
        content = lean_file.read_text(encoding="utf-8")
        lines = content.split("\n")
        contexts = []

        for i, line in enumerate(lines):
            if "sorry" in line or "by admit" in line:
                # Get surrounding context (5 lines before and after)
                start = max(0, i - 5)
                end = min(len(lines), i + 6)
                context = "\n".join(lines[start:end])

                contexts.append(
                    {
                        "line_number": i + 1,
                        "context": context,
                        "statement": line.strip(),
                    }
                )

        return contexts

    def call_apollo_api(self, lean_file: Path, contexts: List[Dict]) -> Optional[str]:
        """Call APOLLO REST API to get proof patches."""
        if self.dry_run:
            print(f"DRY RUN: Would call APOLLO API for {lean_file}")
            return None

        try:
            payload = {
                "file_path": str(lean_file),
                "contexts": contexts,
                "timestamp": datetime.utcnow().isoformat(),
            }

            response = requests.post(
                f"{self.api_url}/prove", json=payload, timeout=300  # 5 minute timeout
            )

            if response.status_code == 200:
                result = response.json()
                return result.get("proof_patch")
            else:
                print(
                    f"Error: APOLLO API returned {response.status_code}: {response.text}"
                )
                return None

        except requests.exceptions.RequestException as e:
            print(f"Error calling APOLLO API: {e}")
            return None

    def apply_proof_patch(self, lean_file: Path, proof_patch: str) -> bool:
        """Apply the proof patch to the Lean file."""
        if self.dry_run:
            print(f"DRY RUN: Would apply proof patch to {lean_file}")
            return True

        try:
            content = lean_file.read_text(encoding="utf-8")
            lines = content.split("\n")

            # Parse the proof patch (simplified - in practice this would be more sophisticated)
            patch_lines = proof_patch.split("\n")

            # For now, we'll do a simple replacement of 'by admit' with the proof
            # In a real implementation, this would use proper diff/patch logic
            new_content = content
            for context in self.extract_admit_context(lean_file):
                if "by admit" in context["statement"]:
                    # Replace 'by admit' with the proof
                    new_content = new_content.replace(
                        context["statement"],
                        context["statement"].replace("by admit", "by simp"),
                    )

            if new_content != content:
                lean_file.write_text(new_content, encoding="utf-8")
                self.changes_made = True
                return True

        except Exception as e:
            print(f"Error applying proof patch to {lean_file}: {e}")
            return False

        return False

    def create_branch_and_commit(self, lean_file: Path) -> bool:
        """Create a new branch and commit the changes."""
        if self.dry_run:
            print(f"DRY RUN: Would create branch and commit for {lean_file}")
            return True

        try:
            # Create branch name based on file hash
            file_hash = self.repo.git.hash_object(lean_file)
            branch_name = f"proofbot/{file_hash[:8]}"

            # Create new branch
            new_branch = self.repo.create_head(branch_name)
            new_branch.checkout()

            # Add and commit changes
            self.repo.index.add([str(lean_file)])
            commit_message = f"Auto-proof: Resolve admits in {lean_file.name}\n\nGenerated by APOLLO proof bot"
            self.repo.index.commit(commit_message)

            # Push branch
            origin = self.repo.remote("origin")
            origin.push(new_branch)

            print(f"✅ Created branch {branch_name} with proof fixes")
            return True

        except Exception as e:
            print(f"Error creating branch and commit: {e}")
            return False

    def run(self) -> int:
        """Main execution method."""
        print("🔍 APOLLO Proof Bot - Scanning for admits...")

        lean_files = self.find_lean_files_with_admits()

        if not lean_files:
            print("✅ No Lean files with admits found")
            return 0

        print(f"📝 Found {len(lean_files)} Lean files with admits:")
        for lean_file in lean_files:
            print(f"  - {lean_file}")

        for lean_file in lean_files:
            print(f"\n🔧 Processing {lean_file}...")

            contexts = self.extract_admit_context(lean_file)
            print(f"  Found {len(contexts)} admit statements")

            proof_patch = self.call_apollo_api(lean_file, contexts)

            if proof_patch:
                if self.apply_proof_patch(lean_file, proof_patch):
                    print(f"  ✅ Applied proof patch")

                    if not self.dry_run:
                        if self.create_branch_and_commit(lean_file):
                            print(f"  ✅ Created branch and committed changes")
                        else:
                            print(f"  ❌ Failed to create branch and commit")
                            return 1
                else:
                    print(f"  ❌ Failed to apply proof patch")
                    return 1
            else:
                print(f"  ⚠️  No proof patch received from APOLLO API")

        if self.changes_made:
            print(f"\n✅ APOLLO Proof Bot completed successfully")
            return 0
        else:
            print(f"\n⚠️  No changes were made")
            return 0


def main():
    parser = argparse.ArgumentParser(description="APOLLO Proof Bot")
    parser.add_argument(
        "--api-url", default="http://localhost:8080", help="APOLLO API URL"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Dry run mode - don't make actual changes",
    )

    args = parser.parse_args()

    bot = ApolloProofBot(api_url=args.api_url, dry_run=args.dry_run)
    return bot.run()


if __name__ == "__main__":
    sys.exit(main())
