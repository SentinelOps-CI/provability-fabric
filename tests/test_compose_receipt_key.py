"""Negative controls for file-backed Compose receipt signing and smoke cleanup."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
COMPOSE = ROOT / "docker-compose.yml"
SMOKE = ROOT / "scripts" / "docker-compose-smoke.sh"


class ReceiptSigningComposeTests(unittest.TestCase):
    """Protect against a reintroduced public receipt-signing seed."""

    def test_retrieval_has_only_file_backed_private_key(self) -> None:
        compose = COMPOSE.read_text(encoding="utf-8")
        match = re.search(
            r"(?ms)^  retrieval-gateway:\n(.*?)(?=^  [a-z][a-z0-9-]*:\n|^volumes:|^secrets:|\Z)",
            compose,
        )
        self.assertIsNotNone(match)
        service = match.group(1)
        self.assertNotIn("RECEIPT_SIGNING_KEY=", service)
        self.assertIn("RECEIPT_SIGNING_KEY_PATH=/run/secrets/retrieval_receipt_signing_key", service)
        self.assertIn("source: retrieval_receipt_signing_key", service)
        self.assertIn("mode: 0400", service)
        self.assertIn("PF_RECEIPT_SIGNING_KEY_FILE", compose)
        self.assertNotIn("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=", compose)

    def test_local_key_files_are_excluded_from_git_and_docker(self) -> None:
        self.assertIn(".local/secrets/", (ROOT / ".gitignore").read_text(encoding="utf-8"))
        self.assertIn(
            "/.local/secrets/**",
            (ROOT / ".dockerignore").read_text(encoding="utf-8"),
        )

    @unittest.skipUnless(
        os.name == "posix" and shutil.which("bash") and shutil.which("dirname"),
        "POSIX Bash and dirname are required for this shell negative control",
    )
    def test_missing_docker_is_failure_not_skip(self) -> None:
        """The Compose smoke must reject a runner without the Docker CLI."""
        with tempfile.TemporaryDirectory(prefix="pf-no-docker-") as tmp:
            fake_bin = Path(tmp) / "bin"
            fake_bin.mkdir()
            (fake_bin / "dirname").symlink_to(shutil.which("dirname"))
            env = os.environ.copy()
            env["PATH"] = str(fake_bin)
            completed = subprocess.run(
                [shutil.which("bash"), str(SMOKE), "full"],
                env=env,
                text=True,
                capture_output=True,
                check=False,
                timeout=10,
            )
            self.assertEqual(completed.returncode, 2, completed.stdout + completed.stderr)
            self.assertIn("ERROR: docker is required", completed.stderr)
            self.assertNotIn("smoke passed", completed.stdout)
            self.assertNotIn("SKIP", completed.stderr)

    @unittest.skipUnless(shutil.which("openssl"), "OpenSSL is unavailable")
    def test_smoke_generates_then_deletes_key(self) -> None:
        completed, calls, key_path = self._execute_smoke()
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("docker-compose smoke passed", completed.stdout)
        self.assertTrue(any(" up " in f" {c} " for c in calls))
        self.assertTrue(any(" down " in f" {c} " for c in calls))
        self.assertFalse(key_path.exists())

    @unittest.skipUnless(shutil.which("openssl"), "OpenSSL is unavailable")
    def test_failed_container_start_cleans_up_secret_and_services(self) -> None:
        completed, calls, key_path = self._execute_smoke(fail_up=True)
        self.assertNotEqual(completed.returncode, 0)
        self.assertTrue(any(" down " in f" {c} " for c in calls))
        self.assertNotIn("docker-compose smoke passed", completed.stdout)
        self.assertFalse(key_path.exists())

    @unittest.skipUnless(shutil.which("openssl"), "OpenSSL is unavailable")
    def test_unhealthy_retrieval_is_failure_and_cleans_up(self) -> None:
        completed, calls, key_path = self._execute_smoke(fail_gateway=True)
        self.assertNotEqual(completed.returncode, 0)
        self.assertTrue(any(" down " in f" {c} " for c in calls))
        self.assertNotIn("docker-compose smoke passed", completed.stdout)
        self.assertFalse(key_path.exists())

    @unittest.skipUnless(shutil.which("openssl"), "OpenSSL is unavailable")
    def test_unhealthy_ledger_is_failure_and_cleans_up(self) -> None:
        completed, calls, key_path = self._execute_smoke(fail_ledger=True)
        self.assertNotEqual(completed.returncode, 0)
        self.assertTrue(any(" down " in f" {c} " for c in calls))
        self.assertNotIn("docker-compose smoke passed", completed.stdout)
        self.assertFalse(key_path.exists())

    def _execute_smoke(
        self, *, fail_up: bool = False, fail_gateway: bool = False, fail_ledger: bool = False
    ) -> tuple[subprocess.CompletedProcess[str], list[str], Path]:
        """Execute the actual shell script with isolated fake network tooling."""
        with tempfile.TemporaryDirectory(prefix="pf-receipt-smoke-") as tmp:
            root = Path(tmp)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copyfile(SMOKE, scripts / SMOKE.name)
            (scripts / "check_wiring.py").write_text(
                "print('fixture wiring valid')\n", encoding="utf-8"
            )
            fake_bin = root / "fake-bin"
            fake_bin.mkdir()
            docker = fake_bin / "docker"
            docker.write_text(
                '#!/usr/bin/env bash\n'
                'set -euo pipefail\n'
                'test -n "$PF_RECEIPT_SIGNING_KEY_FILE"\n'
                'test -s "$PF_RECEIPT_SIGNING_KEY_FILE"\n'
                'grep -q "BEGIN PRIVATE KEY" "$PF_RECEIPT_SIGNING_KEY_FILE"\n'
                'test "$(stat -c %a "$PF_RECEIPT_SIGNING_KEY_FILE")" = 600\n'
                'printf "%s|%s\\n" "$*" "$PF_RECEIPT_SIGNING_KEY_FILE" >> "$MOCK_DOCKER_LOG"\n'
                'if [[ " $* " == *" up "* && "$MOCK_FAIL_UP" == 1 ]]; then exit 42; fi\n',
                encoding="utf-8",
            )
            docker.chmod(0o755)
            curl = fake_bin / "curl"
            curl.write_text(
                '#!/usr/bin/env bash\n'
                'if [[ "$MOCK_FAIL_GATEWAY" == 1 && " $* " == *":8080/health"* ]]; '
                'then exit 22; fi\n'
                'if [[ "$MOCK_FAIL_LEDGER" == 1 && " $* " == *":4000/health"* ]]; '
                'then exit 23; fi\n'
                'exit 0\n',
                encoding="utf-8",
            )
            curl.chmod(0o755)
            log = root / "docker-calls.txt"
            env = os.environ.copy()
            env.update(
                PATH=f"{fake_bin}:{os.environ['PATH']}",
                MOCK_DOCKER_LOG=str(log),
                MOCK_FAIL_UP="1" if fail_up else "0",
                MOCK_FAIL_GATEWAY="1" if fail_gateway else "0",
                MOCK_FAIL_LEDGER="1" if fail_ledger else "0",
            )
            completed = subprocess.run(
                ["bash", str(scripts / SMOKE.name), "full"],
                cwd=root,
                env=env,
                text=True,
                capture_output=True,
                check=False,
                timeout=45,
            )
            self.assertTrue(log.is_file(), completed.stdout + completed.stderr)
            rows = [row.split("|", 1) for row in log.read_text().splitlines()]
            paths = {path for _, path in rows}
            self.assertEqual(len(paths), 1, "Every command needs the same ephemeral key")
            key_path = Path(next(iter(paths)))
            self.assertNotIn(str(key_path), completed.stdout)
            return completed, [command for command, _ in rows], key_path


if __name__ == "__main__":
    unittest.main()
