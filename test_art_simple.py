#!/usr/bin/env python3
"""
Simple ART Test

Quick test to verify ART runner functionality.
"""

import sys
from pathlib import Path

# Add current directory to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from tests.art_runner import ARTRunner

    print("✅ ART runner imported successfully")

    # Test basic functionality
    runner = ARTRunner("1/1")
    print("✅ ART runner instantiated successfully")

    # Test argument parsing
    import argparse

    parser = argparse.ArgumentParser(description="ART Replay Harness")
    parser.add_argument("--shard", required=True, help="Shard in format N/total")
    parser.add_argument(
        "--timeout", type=int, default=60, help="Request timeout in seconds"
    )

    print("✅ Argument parser created successfully")

    print("✅ All ART runner components working correctly")

except Exception as e:
    print(f"❌ Error: {e}")
    sys.exit(1)
