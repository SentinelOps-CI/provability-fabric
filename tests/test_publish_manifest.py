# SPDX-License-Identifier: Apache-2.0
from __future__ import annotations

import tempfile
from pathlib import Path

from experiments.scripts.publish_manifest import (
    verify_publish_manifest_sha256,
    write_publish_manifest_sha256,
)


def test_write_then_verify_roundtrip():
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "a.txt").write_text("hello", encoding="utf-8")
        (root / "sub").mkdir()
        (root / "sub" / "b.txt").write_text("world", encoding="utf-8")
        write_publish_manifest_sha256(root)
        assert (root / "MANIFEST.sha256").exists()
        assert verify_publish_manifest_sha256(root) == []


def test_verify_detects_tamper():
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "x.txt").write_text("v1", encoding="utf-8")
        write_publish_manifest_sha256(root)
        (root / "x.txt").write_text("v2", encoding="utf-8")
        errs = verify_publish_manifest_sha256(root)
        assert len(errs) >= 1
        assert "mismatch" in errs[0].lower() or "hash" in errs[0].lower()
