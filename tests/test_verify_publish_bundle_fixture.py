# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Verifier test: run verify_publish_bundle.py against experiments/fixtures/verify_publish_bundle/
# so changes to publish_bundle.py or verify_publish_bundle.py are regression-tested in CI.

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_PUBLISH = REPO_ROOT / "experiments" / "fixtures" / "verify_publish_bundle" / "publish"
FIXTURE_COMPARE = REPO_ROOT / "experiments" / "fixtures" / "verify_publish_bundle" / "compare.json"


def test_verify_publish_bundle_against_fixture_exit_zero():
    """Invoke verify_publish_bundle.py with fixture publish dir and compare.json; assert exit 0."""
    assert FIXTURE_PUBLISH.is_dir(), "Fixture publish dir missing: %s" % FIXTURE_PUBLISH
    assert FIXTURE_COMPARE.exists(), "Fixture compare.json missing: %s" % FIXTURE_COMPARE
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "experiments" / "scripts" / "verify_publish_bundle.py"),
            "--publish-dir",
            str(FIXTURE_PUBLISH),
            "--compare-json",
            str(FIXTURE_COMPARE),
            "--skip-run-dir-check",
        ],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, "verify_publish_bundle failed: stderr=%s stdout=%s" % (
        proc.stderr,
        proc.stdout,
    )
