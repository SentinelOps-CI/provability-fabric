#!/usr/bin/env python3
"""
CERT-V1 Schema Validation Tool

This tool validates JSON files against the CERT-V1 schema from the external
standards.
"""

import json
import sys
import argparse
import glob
from pathlib import Path
from jsonschema import validate, ValidationError


def load_schema(schema_path):
    """Load the CERT-V1 schema from the external standards directory."""
    try:
        with open(schema_path, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Error loading schema from {schema_path}: {e}")
        sys.exit(1)


def validate_file(file_path, schema):
    """Validate a single JSON file against the schema."""
    try:
        with open(file_path, "r") as f:
            data = json.load(f)

        validate(instance=data, schema=schema)
        print(f"✓ {file_path}")
        return True
    except ValidationError as e:
        print(f"✗ {file_path}: {e.message}")
        return False
    except json.JSONDecodeError as e:
        print(f"✗ {file_path}: Invalid JSON - {e}")
        return False
    except Exception as e:
        print(f"✗ {file_path}: Unexpected error - {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Validate JSON files against CERT-V1 schema"
    )
    parser.add_argument(
        "files", nargs="+", help="JSON files or glob patterns to validate"
    )
    parser.add_argument(
        "--schema",
        default="external/CERT-V1/schema/cert-v1.schema.json",
        help="Path to CERT-V1 schema file",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    # Load schema
    if args.verbose:
        print(f"Loading schema from: {args.schema}")

    schema = load_schema(args.schema)

    if args.verbose:
        print("Schema loaded successfully")

    # Expand glob patterns
    all_files = []
    for pattern in args.files:
        if "*" in pattern or "?" in pattern:
            all_files.extend(glob.glob(pattern, recursive=True))
        else:
            all_files.append(pattern)

    # Filter to only JSON files
    json_files = [f for f in all_files if f.endswith(".json")]

    if args.verbose:
        print("Found {} JSON files to validate".format(len(json_files)))

    # Validate each file
    failed_count = 0
    for file_path in json_files:
        if not Path(file_path).exists():
            print(f"Warning: File {file_path} does not exist")
            continue

        if not validate_file(file_path, schema):
            failed_count += 1

    # Summary
    total_count = len(json_files)
    passed_count = total_count - failed_count

    print("\nValidation Summary:")
    print("  Total files: {}".format(total_count))
    print("  Passed: {}".format(passed_count))
    print("  Failed: {}".format(failed_count))

    if failed_count > 0:
        print("\n❌ Validation failed with {} errors".format(failed_count))
        sys.exit(1)
    else:
        print("\n✅ All files validated successfully")
        sys.exit(0)


if __name__ == "__main__":
    main()
