# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Predictions / resume helpers (lightweight error-recovery semantics).

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.predictions_writer import append_raw_predictions_line


def test_append_raw_predictions_line_idempotent_line_shape():
    with tempfile.TemporaryDirectory() as tmp:
        p = str(Path(tmp) / "out.jsonl")
        line = json.dumps({"instance_id": "i", "model_patch": "", "model_name_or_path": "m"})
        append_raw_predictions_line(p, line)
        append_raw_predictions_line(p, line)
        lines = Path(p).read_text(encoding="utf-8").strip().splitlines()
        assert len(lines) == 2
        assert json.loads(lines[0]) == json.loads(lines[1])
