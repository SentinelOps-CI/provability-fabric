#!/usr/bin/env python3
"""
ART Dataset Fetcher

Downloads the Agent Red Teaming (ART) dataset from Gray Swan S3 and caches it
locally. Verifies SHA256 checksum to ensure data integrity.
"""

import argparse
import hashlib
import sys
from pathlib import Path
from typing import Optional

import boto3
import requests


class ARTFetcher:
    """Fetches and validates the ART dataset from Gray Swan S3."""

    # ART dataset configuration
    S3_BUCKET = "gray-swan-art"
    S3_KEY = "art_dataset.jsonl"
    EXPECTED_SHA256 = "PLACEHOLDER_SHA256_HASH"  # TODO: Replace with actual hash
    CACHE_DIR = Path.home() / ".cache" / "art"
    CACHE_FILE = CACHE_DIR / "art_dataset.jsonl"

    def __init__(self):
        self.s3_client = boto3.client("s3")

    def download_from_s3(self) -> bool:
        """Download dataset from S3 to cache directory."""
        try:
            print(f"Downloading {self.S3_KEY} from {self.S3_BUCKET}...")

            # Ensure cache directory exists
            self.CACHE_DIR.mkdir(parents=True, exist_ok=True)

            # Download file
            self.s3_client.download_file(
                self.S3_BUCKET, self.S3_KEY, str(self.CACHE_FILE)
            )

            print(f"Downloaded to {self.CACHE_FILE}")
            return True

        except Exception as e:
            print(f"Error downloading from S3: {e}")
            return False

    def download_from_url(self, url: str) -> bool:
        """Download dataset from URL as fallback."""
        try:
            print(f"Downloading from URL: {url}")

            # Ensure cache directory exists
            self.CACHE_DIR.mkdir(parents=True, exist_ok=True)

            # Download file
            response = requests.get(url, stream=True)
            response.raise_for_status()

            with open(self.CACHE_FILE, "wb") as f:
                for chunk in response.iter_content(chunk_size=8192):
                    f.write(chunk)

            print(f"Downloaded to {self.CACHE_FILE}")
            return True

        except Exception as e:
            print(f"Error downloading from URL: {e}")
            return False

    def calculate_sha256(self, file_path: Path) -> str:
        """Calculate SHA256 hash of file."""
        sha256_hash = hashlib.sha256()

        with open(file_path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                sha256_hash.update(chunk)

        return sha256_hash.hexdigest()

    def verify_checksum(self, file_path: Path) -> bool:
        """Verify file SHA256 checksum matches expected value."""
        if self.EXPECTED_SHA256 == "PLACEHOLDER_SHA256_HASH":
            print("Warning: Using placeholder SHA256 hash. Verification skipped.")
            return True

        actual_hash = self.calculate_sha256(file_path)
        expected_hash = self.EXPECTED_SHA256.lower()

        if actual_hash == expected_hash:
            print(f"✓ Checksum verified: {actual_hash}")
            return True
        else:
            print("✗ Checksum mismatch!")
            print(f"  Expected: {expected_hash}")
            print(f"  Actual:   {actual_hash}")
            return False

    def fetch(self, force: bool = False, url: Optional[str] = None) -> bool:
        """Fetch ART dataset and verify integrity."""

        # Check if file already exists and is valid
        if self.CACHE_FILE.exists() and not force:
            print(f"Dataset already cached at {self.CACHE_FILE}")
            if self.verify_checksum(self.CACHE_FILE):
                return True
            else:
                print("Cached file has invalid checksum, re-downloading...")

        # Download dataset
        success = False
        if url:
            success = self.download_from_url(url)
        else:
            success = self.download_from_s3()

        if not success:
            print("Failed to download dataset")
            return False

        # Verify checksum
        if not self.verify_checksum(self.CACHE_FILE):
            print("Downloaded file failed checksum verification")
            return False

        print("✓ ART dataset successfully fetched and verified")
        return True

    def get_dataset_path(self) -> Optional[Path]:
        """Get path to cached dataset if it exists and is valid."""
        if not self.CACHE_FILE.exists():
            return None

        if not self.verify_checksum(self.CACHE_FILE):
            return None

        return self.CACHE_FILE


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Fetch ART dataset from Gray Swan S3")
    parser.add_argument(
        "--verify", action="store_true", help="Verify cached dataset checksum"
    )
    parser.add_argument(
        "--force", action="store_true", help="Force re-download even if cached"
    )
    parser.add_argument("--url", help="Alternative download URL (fallback)")
    parser.add_argument("--path", help="Show path to cached dataset")

    args = parser.parse_args()

    fetcher = ARTFetcher()

    if args.path:
        dataset_path = fetcher.get_dataset_path()
        if dataset_path:
            print(str(dataset_path))
            return 0
        else:
            print("No valid cached dataset found", file=sys.stderr)
            return 1

    if args.verify:
        if not fetcher.CACHE_FILE.exists():
            print("No cached dataset found", file=sys.stderr)
            return 1

        if fetcher.verify_checksum(fetcher.CACHE_FILE):
            print("✓ Dataset checksum verified")
            return 0
        else:
            print("✗ Dataset checksum verification failed", file=sys.stderr)
            return 1

    # Fetch dataset
    success = fetcher.fetch(force=args.force, url=args.url)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
