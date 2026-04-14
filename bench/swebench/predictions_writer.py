# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# predictions.jsonl and related append helpers.

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def pfmeta_path(predictions_out_path: str) -> Path:
    """Sidecar path: predictions.jsonl -> predictions.pfmeta.jsonl."""
    p = Path(predictions_out_path)
    return p.parent / (p.stem + ".pfmeta.jsonl")


class PredictionsWriter:
    """Append SWE-bench prediction lines to a JSONL file."""

    def __init__(self, out_path: str):
        self.out_path = out_path

    def write_line(self, instance_id: str, model_patch: str, model_name: str) -> None:
        line = (
            json.dumps(
                {
                    "instance_id": instance_id,
                    "model_patch": model_patch,
                    "model_name_or_path": model_name,
                },
                ensure_ascii=False,
            )
            + "\n"
        )
        with open(self.out_path, "a", encoding="utf-8") as f:
            f.write(line)

    def append_raw_line(self, raw_line: str) -> None:
        with open(self.out_path, "a", encoding="utf-8") as f:
            f.write(raw_line.rstrip("\n") + "\n")


def emit_predictions_line(out_path: str, instance_id: str, model_patch: str, model_name: str) -> None:
    """Append one line in SWE-bench predictions.jsonl format."""
    PredictionsWriter(out_path).write_line(instance_id, model_patch, model_name)


def append_raw_predictions_line(out_path: str, raw_line: str) -> None:
    """Append a pre-formed predictions line (for --skip-existing resume)."""
    PredictionsWriter(out_path).append_raw_line(raw_line)


def write_pfmeta_jsonl(pfmeta_path: Path, lines: list[dict[str, Any]]) -> None:
    pfmeta_path = Path(pfmeta_path)
    pfmeta_path.parent.mkdir(parents=True, exist_ok=True)
    with open(pfmeta_path, "w", encoding="utf-8") as f:
        for rec in lines:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
