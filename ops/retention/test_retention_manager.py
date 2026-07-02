#!/usr/bin/env python3
"""Unit tests for ops/retention/retention_manager.py (F39)."""

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest.mock import MagicMock

# retention_manager imports cloud/DB stacks; stub for unit tests of pure helpers.
for _mod in (
    "yaml",
    "psycopg2",
    "boto3",
    "google",
    "google.cloud",
    "google.cloud.bigquery",
    "pandas",
    "pyarrow",
    "pyarrow.parquet",
):
    sys.modules.setdefault(_mod, MagicMock())

ROOT = Path(__file__).resolve().parents[2]
MODULE_PATH = ROOT / "ops" / "retention" / "retention_manager.py"

spec = importlib.util.spec_from_file_location("retention_manager", MODULE_PATH)
retention_manager = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(retention_manager)


class TestValidateTableName(unittest.TestCase):
    def test_rejects_empty(self) -> None:
        with self.assertRaises(ValueError):
            retention_manager._validate_table_name("", {"usage_events"})

    def test_rejects_invalid_identifier(self) -> None:
        with self.assertRaises(ValueError):
            retention_manager._validate_table_name("UsageEvents", {"usage_events"})
        with self.assertRaises(ValueError):
            retention_manager._validate_table_name("usage-events", {"usage_events"})

    def test_rejects_not_in_allowlist(self) -> None:
        with self.assertRaises(ValueError):
            retention_manager._validate_table_name(
                "arbitrary_table", {"usage_events", "audit_log"}
            )

    def test_accepts_allowlisted_name(self) -> None:
        retention_manager._validate_table_name(
            "usage_events", {"usage_events", "audit_log"}
        )


if __name__ == "__main__":
    unittest.main()
