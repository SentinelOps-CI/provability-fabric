# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Patch apply-check and validation edge cases (no full git repo required for some paths).

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.runner import run_patch_apply_check


def test_patch_apply_check_empty_patch_stderr():
    applies, rep = run_patch_apply_check(Path("/nonexistent/not-a-repo"), "", "a", "b")
    assert applies is False
    assert rep.get("stderr") == "empty patch" or "empty" in (rep.get("stderr") or "").lower()


@pytest.mark.parametrize(
    "patch_content,expect_applies_false",
    [
        ("", True),
        ("   \n  \n", True),
    ],
)
def test_patch_apply_check_whitespace_only_patch(patch_content: str, expect_applies_false: bool):
    applies, rep = run_patch_apply_check(Path("/nonexistent/path"), patch_content, "a", "b")
    assert applies is (not expect_applies_false) or rep.get("applies") is False
