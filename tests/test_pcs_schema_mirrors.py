"""Check canonical PCS schema and dual-mirror consistency with isolated fixtures."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "scripts" / "pcs-schema-diff.sh"
SCHEMA = '{"type":"object"}\n'


class PCSSchemaMirrorsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repo"
        self.canonical = Path(self.temp.name) / "pcs-core" / "schemas"
        self.config = self.root / "config" / "schemas" / "pcs"
        self.mirror = self.root / "adapters" / "pcs" / "schemas"
        for path in (self.root / "scripts", self.canonical, self.config, self.mirror):
            path.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE, self.root / "scripts" / "pcs-schema-diff.sh")
        for path in (self.canonical, self.config, self.mirror):
            (path / "base.json").write_text(SCHEMA, encoding="utf-8")

    def run_checker(self):
        return subprocess.run(
            ["bash", str(self.root / "scripts" / "pcs-schema-diff.sh")],
            capture_output=True,
            text=True,
            cwd=self.root,
            env={"PATH": "/usr/bin:/bin", "PCS_CORE_SCHEMAS": str(self.canonical)},
            check=False,
            timeout=10,
        )

    def test_matching_mirrors_pass(self):
        result = self.run_checker()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("config schema mirror", result.stdout)

    def test_changed_adapter_copy_is_detected(self):
        (self.mirror / "base.json").write_text('{"type":"string"}\n')
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("adapter schema mirror drift", result.stderr)

    def test_missing_adapter_copy_is_detected(self):
        (self.mirror / "base.json").unlink()
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing adapter schema mirror", result.stderr)

    def test_orphaned_adapter_copy_is_detected(self):
        (self.mirror / "extra.json").write_text(SCHEMA)
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("orphaned adapter schema mirror", result.stderr)

    def test_config_only_profile_is_allowed(self):
        profile = self.config / "profiles" / "extension.json"
        profile.parent.mkdir()
        profile.write_text(SCHEMA)
        result = self.run_checker()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_empty_canonical_directory_fails(self):
        (self.canonical / "base.json").unlink()
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("contains no JSON schemas", result.stderr)

    def test_canonical_drift_still_fails(self):
        (self.config / "base.json").write_text('{"type":"string"}\n')
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("schema drift", result.stderr)


if __name__ == "__main__":
    unittest.main()
