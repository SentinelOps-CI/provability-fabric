# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.predictions_writer import (
    PredictionsWriter,
    emit_predictions_line,
    pfmeta_path,
    write_pfmeta_jsonl,
)


def test_predictions_writer_line_schema():
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "pred.jsonl"
        w = PredictionsWriter(str(p))
        w.write_line("id1", "diff", "model-x")
        line = p.read_text(encoding="utf-8").strip()
        obj = json.loads(line)
        assert obj == {"instance_id": "id1", "model_patch": "diff", "model_name_or_path": "model-x"}


def test_emit_predictions_line_alias():
    with tempfile.TemporaryDirectory() as tmp:
        p = str(Path(tmp) / "o.jsonl")
        emit_predictions_line(p, "i", "d", "m")
        assert "i" in Path(p).read_text(encoding="utf-8")


def test_pfmeta_path_and_write():
    with tempfile.TemporaryDirectory() as tmp:
        out = str(Path(tmp) / "predictions.jsonl")
        assert pfmeta_path(out).name == "predictions.pfmeta.jsonl"
        mpath = Path(tmp) / "m.jsonl"
        write_pfmeta_jsonl(mpath, [{"instance_id": "1", "x": 1}])
        assert json.loads(mpath.read_text(encoding="utf-8").strip())["instance_id"] == "1"
