# SPDX-License-Identifier: Apache-2.0
"""Exercise vendor retry control flow with isolated command stubs."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/vendor-mathlib.sh"
PIN = "a45ae63747140c1b2cbad9d46f518015c047047a"


class VendorMathlibCacheTests(unittest.TestCase):
    def run_vendor(self, failed_attempts: int, revision: str = PIN):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            vendor = root / "vendor/mathlib"
            (vendor / ".git").mkdir(parents=True)
            (vendor / ".lake/build/lib").mkdir(parents=True)
            (vendor / ".lake/build/lib/partial.olean").touch()
            (vendor / "lakefile.lean").touch()
            bin_dir = root / "bin"
            bin_dir.mkdir()
            stubs = {
                "git": '#!/bin/bash\nif [[ "$*" == "rev-parse HEAD" ]]; then echo "$TEST_REVISION"; else exit 1; fi\n',
                "timeout": '#!/bin/bash\n[[ "$1" == --kill-after=* ]] && shift\nshift\nexec "$@"\n',
                "sleep": "#!/bin/bash\nexit 0\n",
                "lake": """#!/bin/bash
set -eu
test "$*" = "exe cache get"
n=0
if [ -f "$TEST_COUNT" ]; then n=$(cat "$TEST_COUNT"); fi
n=$((n+1))
echo "$n" > "$TEST_COUNT"
if [ "$n" -le "$TEST_FAILURES" ]; then exit 23; fi
""",
            }
            for name, source in stubs.items():
                path = bin_dir / name
                path.write_text(source, encoding="utf-8")
                path.chmod(0o755)
            count = root / "attempts"
            env = dict(os.environ, PATH=f"{bin_dir}:{os.environ['PATH']}",
                       TEST_REVISION=revision, TEST_COUNT=str(count),
                       TEST_FAILURES=str(failed_attempts))
            result = subprocess.run(
                ["bash", str(SCRIPT)], cwd=root, env=env,
                capture_output=True, text=True, timeout=15, check=False,
            )
            attempts = int(count.read_text()) if count.exists() else 0
            return result, attempts

    def test_partial_build_directory_does_not_skip_retrieval(self):
        result, attempts = self.run_vendor(0)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(attempts, 1)

    def test_transient_failure_is_retried(self):
        result, attempts = self.run_vendor(2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(attempts, 3)

    def test_exhausted_retries_fail_closed(self):
        result, attempts = self.run_vendor(3)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(attempts, 3)
        self.assertNotIn("Mathlib vendored successfully", result.stdout)

    def test_wrong_revision_does_not_retrieve(self):
        result, attempts = self.run_vendor(0, revision="wrong")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(attempts, 0)


if __name__ == "__main__":
    unittest.main()
