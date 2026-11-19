"""Regression tests for non-destructive Criterion baseline metadata updates."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest

SCRIPT = (
    Path(__file__).resolve().parents[1] / "scripts" / "record_criterion_baseline.py"
)
spec = importlib.util.spec_from_file_location("record_criterion_baseline", SCRIPT)
assert spec is not None and spec.loader is not None
baseline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline)

SHA = "a" * 40
BASELINE = (
    "# Criterion Baseline\n\n"
    "Preserve existing proof-run citations and explanatory text.\n\n"
    "| Field | Value |\n|---|---|\n"
    "| Last refresh SHA | `old` |\n"
    "| Last refresh date (UTC) | old date |\n"
    "| Last refresh machine | old host |\n"
    "| Workflow | `bench-nightly-criterion.yaml` |\n"
    "| Proof runs | historical evidence |\n"
)


class BaselineUpdaterTests(unittest.TestCase):
    def update(self, text: str) -> str:
        return baseline.update_baseline_document(
            text, sha=SHA, date="2026-11-19T08:00:00Z", machine="Linux x86_64",
        )

    def test_updates_only_expected_cells(self):
        result = self.update(BASELINE)
        self.assertIn(f"| Last refresh SHA | `{SHA}` |", result)
        self.assertIn("| Last refresh date (UTC) | 2026-11-19T08:00:00Z |", result)
        self.assertIn("| Last refresh machine | Linux x86_64 |", result)
        self.assertIn("| Proof runs | historical evidence |", result)
        self.assertIn("Preserve existing proof-run citations", result)
        self.assertEqual(result.count("| Workflow |"), 1)

    def test_refuses_missing_or_duplicate_rows(self):
        missing = BASELINE.replace("| Last refresh machine | old host |\n", "")
        duplicate = BASELINE + "| Last refresh machine | duplicate |\n"
        for content in (missing, duplicate):
            with self.subTest(content=content), self.assertRaises(ValueError):
                self.update(content)

    def test_invalid_metadata_is_rejected(self):
        for kwargs in (
            {"sha": "short", "date": "2026-11-19T08:00:00Z", "machine": "Linux"},
            {"sha": SHA, "date": "unqualified", "machine": "Linux"},
            {"sha": SHA, "date": "2026-11-19T08:00:00Z", "machine": "host|broken"},
            {"sha": SHA, "date": "2026-11-19T08:00:00Z", "machine": "host\nrow"},
        ):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                baseline.update_baseline_document(BASELINE, **kwargs)

    def test_failed_validation_keeps_file_unchanged(self):
        with tempfile.TemporaryDirectory() as dirname:
            path = Path(dirname) / "BASELINE.md"
            original = BASELINE.replace("| Last refresh date (UTC) | old date |\n", "")
            path.write_text(original, encoding="utf-8")
            with self.assertRaises(ValueError):
                baseline.record_baseline(
                    path, sha=SHA, date="2026-11-19T08:00:00Z", machine="Linux",
                )
            self.assertEqual(path.read_text(encoding="utf-8"), original)
            self.assertEqual(list(Path(dirname).iterdir()), [path])

    def test_atomic_update_preserves_other_content(self):
        with tempfile.TemporaryDirectory() as dirname:
            path = Path(dirname) / "BASELINE.md"
            path.write_text(BASELINE, encoding="utf-8")
            baseline.record_baseline(
                path, sha=SHA, date="2026-11-19T08:00:00Z", machine="Linux",
            )
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                self.update(BASELINE).replace("Linux x86_64", "Linux"),
            )
            self.assertEqual(list(Path(dirname).iterdir()), [path])

    def test_refuses_missing_or_symlink_record(self):
        with tempfile.TemporaryDirectory() as dirname:
            root = Path(dirname)
            target = root / "BASELINE.md"
            link = root / "baseline-link.md"
            with self.assertRaises(ValueError):
                baseline.record_baseline(
                    target, sha=SHA, date="2026-11-19T08:00:00Z", machine="Linux"
                )
            target.write_text(BASELINE, encoding="utf-8")
            link.symlink_to(target)
            with self.assertRaises(ValueError):
                baseline.record_baseline(
                    link, sha=SHA, date="2026-11-19T08:00:00Z", machine="Linux"
                )


if __name__ == "__main__":
    unittest.main()
