# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Ensure bench/swebench is on sys.path so runner.py script-style imports resolve
# when tests import bench.swebench.* or bench.swebench.runner.

from __future__ import annotations

import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parent.parent
_SWBENCH_DIR = _REPO_ROOT / "bench" / "swebench"
if str(_SWBENCH_DIR) not in sys.path:
    sys.path.insert(0, str(_SWBENCH_DIR))
