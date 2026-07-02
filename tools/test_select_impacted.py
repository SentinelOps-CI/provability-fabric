#!/usr/bin/env python3
"""Unit tests for tools/select_impacted.py (F12)."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import select_impacted  # noqa: E402


class SelectImpactedTests(unittest.TestCase):
    def test_impacted_tests_emit_file_paths_not_tokens(self):
        changed = [
            "tests/integration/test_platform_integration.py",
            "tests/redteam/injection_runner.py",
            "core/cli/pf/main.go",
        ]
        tests = select_impacted.get_impacted_tests(str(ROOT), changed)
        self.assertIn("tests/integration/test_platform_integration.py", tests)
        self.assertIn("tests/redteam/injection_runner.py", tests)
        for item in tests:
            self.assertNotRegex(item, r"^python_test:")
            self.assertTrue(
                item.endswith(".py") or item.endswith(".js") or item.endswith(".rs"),
                msg=f"unexpected test token: {item}",
            )

    def test_json_output_uses_paths(self):
        changed = ["tests/integration/test_billing.py"]
        result = select_impacted.build_result(str(ROOT), changed)
        self.assertIn("tests/integration/test_billing.py", result["impacted_tests"])

    def test_cli_writes_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "impacted.json"
            proc = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "tools" / "select_impacted.py"),
                    "--root",
                    str(ROOT),
                    "--base-ref",
                    "HEAD",
                    "--output",
                    str(out),
                ],
                capture_output=True,
                text=True,
                cwd=ROOT,
            )
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)
            data = json.loads(out.read_text(encoding="utf-8"))
            self.assertIn("impacted_tests", data)


if __name__ == "__main__":
    unittest.main()
