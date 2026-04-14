# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.policy.loader import load_pack, policy_hash

REQUIRED_KEYS = ("name", "version", "allowed_tools", "denied", "budgets", "allowed_binaries")


def test_load_pack_swebench_safe_v1():
    content, sha = load_pack("swebench_safe_v1")
    assert isinstance(content, dict)
    for key in REQUIRED_KEYS:
        assert key in content, "missing key: %s" % key
    assert content.get("name") == "swebench_safe_v1"
    assert content.get("version") == "1"
    assert isinstance(content.get("allowed_tools"), list)
    assert isinstance(content.get("denied"), list)
    assert isinstance(content.get("budgets"), dict)
    assert isinstance(content.get("allowed_binaries"), list)


def test_load_pack_hash_deterministic():
    c1, h1 = load_pack("swebench_safe_v1")
    c2, h2 = load_pack("swebench_safe_v1")
    assert h1 == h2
    assert h1 == policy_hash(c1)


def test_load_pack_unknown_raises():
    with pytest.raises(ValueError, match="Unknown policy pack"):
        load_pack("nonexistent_pack_xyz")


def test_load_pack_missing_file_raises(tmp_path):
    from bench.swebench.policy import loader

    with pytest.raises(FileNotFoundError, match="not found"):
        loader.load_pack("swebench_safe_v1", packs_dir=tmp_path)
