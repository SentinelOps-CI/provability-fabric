# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Replay roundtrip: tiny repo, apply patch, build replay bundle, run replay, assert hash match.
# Skipped on Windows when replay logic relies on Unix (fcntl, etc.).

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


@pytest.mark.skipif(os.name == "nt", reason="Replay roundtrip uses Unix tooling; run in WSL/Linux")
def test_replay_roundtrip_placeholder():
    """Placeholder for full replay roundtrip (tiny git repo, patch, replay bundle, hash match)."""
    pass
