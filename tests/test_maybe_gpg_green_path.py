# SPDX-License-Identifier: Apache-2.0
"""Green-path manifest signing: same hook used by update_run_ids_if_green and publish_manifest."""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

from experiments.scripts.publish_manifest import (
    maybe_gpg_detach_sign_manifest,
    write_publish_manifest_sha256,
)


class TestMaybeGpgDetachSignManifest(unittest.TestCase):
    def test_noop_when_flag_unset(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "x.txt").write_text("a", encoding="utf-8")
            write_publish_manifest_sha256(d)
            asc = d / "MANIFEST.sha256.asc"
            with patch.dict(os.environ, {"PF_GPG_SIGN_MANIFEST": ""}):
                with patch.object(
                    subprocess, "run", side_effect=AssertionError("gpg should not run")
                ):
                    maybe_gpg_detach_sign_manifest(d)
            self.assertFalse(asc.exists())

    def test_invokes_gpg_when_flag_true(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "x.txt").write_text("b", encoding="utf-8")
            write_publish_manifest_sha256(d)
            manifest = d / "MANIFEST.sha256"
            asc = d / "MANIFEST.sha256.asc"
            with patch.dict(os.environ, {"PF_GPG_SIGN_MANIFEST": "1"}, clear=False):
                with patch.object(subprocess, "run") as run_mock:
                    run_mock.return_value = MagicMock(returncode=0, stdout="", stderr="")
                    maybe_gpg_detach_sign_manifest(d)
            run_mock.assert_called_once()
            cmd = run_mock.call_args[0][0]
            self.assertEqual(cmd[0], "gpg")
            self.assertIn("--detach-sign", cmd)
            self.assertIn(str(manifest), cmd)
            self.assertIn(str(asc), cmd)

    def test_key_id_inserted_when_set(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "y.txt").write_text("c", encoding="utf-8")
            write_publish_manifest_sha256(d)
            with patch.dict(
                os.environ,
                {"PF_GPG_SIGN_MANIFEST": "yes", "PF_GPG_KEY_ID": "DEADBEEF"},
                clear=False,
            ):
                with patch.object(subprocess, "run") as run_mock:
                    run_mock.return_value = MagicMock(returncode=0, stdout="", stderr="")
                    maybe_gpg_detach_sign_manifest(d)
            cmd = run_mock.call_args[0][0]
            self.assertIn("--local-user", cmd)
            idx = cmd.index("--local-user")
            self.assertEqual(cmd[idx + 1], "DEADBEEF")


if __name__ == "__main__":
    unittest.main()
