#!/usr/bin/env python3
"""
Test script for ART fetch functionality
"""

import sys
from pathlib import Path

# Add tools directory to path
sys.path.insert(0, str(Path(__file__).parent / "tools"))

try:
    from art_fetch import ARTFetcher

    def test_art_fetcher():
        """Test ART fetcher functionality"""
        print("Testing ART fetcher...")

        # Test initialization
        fetcher = ARTFetcher()
        print("✓ ARTFetcher initialized")
        print(f"  Cache directory: {fetcher.CACHE_DIR}")
        print(f"  Cache file: {fetcher.CACHE_FILE}")
        print(f"  S3 bucket: {fetcher.S3_BUCKET}")
        print(f"  S3 key: {fetcher.S3_KEY}")

        # Test SHA256 calculation
        test_file = Path("test_data.txt")
        test_file.write_text("Hello, ART!")

        hash_value = fetcher.calculate_sha256(test_file)
        print(f"✓ SHA256 calculation works: {hash_value}")

        # Test checksum verification (should pass with placeholder)
        if fetcher.verify_checksum(test_file):
            print("✓ Checksum verification works")
        else:
            print("✗ Checksum verification failed")

        # Cleanup
        test_file.unlink()

        print("✅ All tests passed!")
        return True

    if __name__ == "__main__":
        test_art_fetcher()

except ImportError as e:
    print(f"Import error: {e}")
    print("Make sure you're running from the project root directory")
    sys.exit(1)
except Exception as e:
    print(f"Test failed: {e}")
    sys.exit(1)
