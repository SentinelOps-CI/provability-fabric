"""Verify Go format checking is read-only and detects changed source."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "check_go_format.py"
spec = importlib.util.spec_from_file_location("check_go_format", SCRIPT)
assert spec is not None and spec.loader is not None
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


@unittest.skipUnless(shutil.which("git") and shutil.which("gofmt"), "git and gofmt required")
class GoFormatTests(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.module = self.root / "services" / "spec-service"
        self.module.mkdir(parents=True)
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)

    def add(self, name: str, text: str) -> Path:
        path = self.module / name
        path.write_text(text, encoding="utf-8")
        subprocess.run(["git", "add", "--", str(path.relative_to(self.root))], cwd=self.root, check=True)
        return path

    def check(self) -> list[str]:
        return checker.check_go_format(self.root, ("services/spec-service",))

    def test_formatted_source_passes(self) -> None:
        self.add("main.go", "package main\n\nfunc main() {}\n")
        self.assertEqual(self.check(), [])

    def test_bad_format_fails_without_rewriting(self) -> None:
        source = self.add("main.go", "package main\nfunc main(){println(\"x\")}\n")
        original = source.read_bytes()
        self.assertEqual(self.check(), ["services/spec-service/main.go"])
        self.assertEqual(source.read_bytes(), original)

    def test_untracked_file_is_not_checked(self) -> None:
        self.add("main.go", "package main\n\nfunc main() {}\n")
        (self.module / "local.go").write_text("package main\nfunc local(){ }")
        self.assertEqual(self.check(), [])

    def test_invalid_module_and_empty_index_fail_closed(self) -> None:
        for path in ("../outside", "/tmp", "missing"):
            with self.subTest(path=path), self.assertRaises(checker.FormatCheckError):
                checker.check_go_format(self.root, (path,))
        with self.assertRaises(checker.FormatCheckError):
            self.check()

    def test_multiple_bad_files_are_reported_deterministically(self) -> None:
        self.add("z.go", "package main\nfunc z(){println(1)}\n")
        self.add("a.go", "package main\nfunc a(){println(2)}\n")
        self.assertEqual(self.check(), ["services/spec-service/a.go", "services/spec-service/z.go"])

    def test_cli_returns_status_one_for_unformatted_source(self) -> None:
        self.add("main.go", "package main\nfunc main(){println(1)}\n")
        p = subprocess.run(["python3", str(SCRIPT), "--root", str(self.root), "services/spec-service"], capture_output=True, text=True)
        self.assertEqual(p.returncode, 1, p.stderr)
        self.assertIn("services/spec-service/main.go", p.stderr)


if __name__ == "__main__":
    unittest.main()
