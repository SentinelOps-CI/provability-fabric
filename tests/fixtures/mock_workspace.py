# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Minimal fake workspace layout for tests.

from __future__ import annotations

from pathlib import Path


def make_minimal_workspace_root(base: Path) -> Path:
    """Create base/repo/.git marker (empty file) for path checks."""
    root = Path(base) / "ws"
    repo = root / "repo"
    repo.mkdir(parents=True, exist_ok=True)
    (repo / ".git").write_text("fake\n", encoding="utf-8")
    (root / "scratch").mkdir(parents=True, exist_ok=True)
    return root
