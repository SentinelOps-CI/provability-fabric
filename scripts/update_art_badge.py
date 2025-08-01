#!/usr/bin/env python3
"""
ART Badge Updater

Updates the ART Defence badge in README.md based on benchmark results.
Automatically changes color and status based on performance thresholds.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Optional

import requests


def fetch_latest_metrics() -> Optional[float]:
    """Fetch the latest ART overall block rate from Prometheus."""
    try:
        response = requests.get(
            "http://localhost:9090/api/v1/query",
            params={"query": "art_block_rate_overall"},
        )
        response.raise_for_status()

        data = response.json()
        if data["data"]["result"]:
            return float(data["data"]["result"][0]["value"][1])
        else:
            return None

    except Exception as e:
        print(f"Warning: Could not fetch metrics: {e}")
        return None


def get_badge_color(block_rate: float) -> str:
    """Determine badge color based on block rate."""
    if block_rate >= 99.0:
        return "brightgreen"
    elif block_rate >= 95.0:
        return "yellow"
    else:
        return "red"


def update_readme_badge(block_rate: float) -> bool:
    """Update the ART badge in README.md."""
    readme_path = Path("README.md")

    if not readme_path.exists():
        print("Error: README.md not found")
        return False

    # Read current README
    with open(readme_path, "r") as f:
        content = f.read()

    # Determine badge color and status
    color = get_badge_color(block_rate)
    status = "PASS" if block_rate >= 99.0 else "FAIL"

    # Create new badge
    new_badge = f"[![ART Defence](https://img.shields.io/badge/ART%20Defence-{block_rate:.1f}%25-{color})](https://provability-fabric.org/benchmarks/art)"
    new_status_badge = f"[![ART Status](https://img.shields.io/badge/ART%20Status-{status}-{color})](https://github.com/provability-fabric/provability-fabric/actions/workflows/art-benchmark.yaml)"

    # Replace existing badges
    # Replace ART Defence badge
    art_defence_pattern = r"\[!\[ART Defence\]\(https://img\.shields\.io/badge/ART%20Defence-[^)]+\)\]\([^)]+\)"
    if re.search(art_defence_pattern, content):
        content = re.sub(art_defence_pattern, new_badge, content)
    else:
        # Add after TRUST-FIRE badge
        trust_fire_pattern = r"\[!\[TRUST-FIRE\]\([^)]+\)\]\([^)]+\)"
        if re.search(trust_fire_pattern, content):
            content = re.sub(trust_fire_pattern, f"\\g<0>\n{new_badge}", content)

    # Replace ART Status badge
    art_status_pattern = r"\[!\[ART Status\]\(https://img\.shields\.io/badge/ART%20Status-[^)]+\)\]\([^)]+\)"
    if re.search(art_status_pattern, content):
        content = re.sub(art_status_pattern, new_status_badge, content)
    else:
        # Add after ART Defence badge
        art_defence_pattern = r"\[!\[ART Defence\]\([^)]+\)\]\([^)]+\)"
        if re.search(art_defence_pattern, content):
            content = re.sub(
                art_defence_pattern, f"\\g<0>\n{new_status_badge}", content
            )

    # Write updated README
    with open(readme_path, "w") as f:
        f.write(content)

    print(f"Updated README badges:")
    print(f"  ART Defence: {block_rate:.1f}% ({color})")
    print(f"  ART Status: {status} ({color})")

    return True


def main():
    """Main function to update ART badge."""
    parser = argparse.ArgumentParser(description="Update ART badge in README")
    parser.add_argument("--block-rate", type=float, help="Manual block rate override")
    parser.add_argument(
        "--metrics-url",
        default="http://localhost:9090/api/v1/query",
        help="Prometheus metrics URL",
    )

    args = parser.parse_args()

    # Get block rate
    if args.block_rate is not None:
        block_rate = args.block_rate
    else:
        block_rate = fetch_latest_metrics()
        if block_rate is None:
            print("Error: Could not fetch metrics and no manual override provided")
            sys.exit(1)

    # Update badge
    success = update_readme_badge(block_rate)

    if success:
        print("✅ ART badge updated successfully")
    else:
        print("❌ Failed to update ART badge")
        sys.exit(1)


if __name__ == "__main__":
    main()
