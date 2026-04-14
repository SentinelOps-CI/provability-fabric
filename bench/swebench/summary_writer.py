# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Aggregate summary.json for a run (wraps cost_report.write_summary + fallback).

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable, Optional

try:
    from .constants import PATCH_APPLY_CHECK_FILENAME, SUMMARY_JSON_FILENAME
    from .util import sanitize_instance_id
except ImportError:
    try:
        from bench.swebench.constants import PATCH_APPLY_CHECK_FILENAME, SUMMARY_JSON_FILENAME
        from bench.swebench.util import sanitize_instance_id
    except ImportError:
        from constants import PATCH_APPLY_CHECK_FILENAME, SUMMARY_JSON_FILENAME  # type: ignore[no-redef]
        from util import sanitize_instance_id  # type: ignore[no-redef]


class SummaryWriter:
    """Writes summary.json / uses cost_report when available."""

    def __init__(
        self,
        write_summary_fn: Optional[Callable[..., None]] = None,
    ):
        self._write_summary = write_summary_fn

    def write_run_summary(
        self,
        run_dir: Path,
        cost_reports: list[dict[str, Any]],
        run_id: str,
        guarded: bool,
        *,
        instance_ids_planned: list[str],
        effective_model_name: str,
    ) -> None:
        """Persist summary using cost_report.write_summary or minimal fallback."""
        run_dir = Path(run_dir)
        if cost_reports and self._write_summary is not None:
            self._write_summary(run_dir, cost_reports, run_id, guarded)
            return
        if not cost_reports:
            fallback_ids = [
                iid
                for iid in instance_ids_planned
                if (run_dir / sanitize_instance_id(iid) / PATCH_APPLY_CHECK_FILENAME).exists()
            ]
            if not fallback_ids:
                fallback_ids = list(instance_ids_planned)
            minimal_reports = [
                {
                    "instance_id": iid,
                    "run_id": run_id,
                    "guarded": guarded,
                    "model_name": effective_model_name or "",
                    "prompt_tokens": 0,
                    "completion_tokens": 0,
                    "iterations": 0,
                    "tool_calls": 0,
                    "wall_clock_s": 0.0,
                    "replay_s": 0.0,
                    "proof_s": 0.0,
                }
                for iid in fallback_ids
            ]
            if self._write_summary is not None:
                self._write_summary(run_dir, minimal_reports, run_id, guarded)
            else:
                run_dir.mkdir(parents=True, exist_ok=True)
                summary = {
                    "run_id": run_id,
                    "guarded": guarded,
                    "n_instances": len(minimal_reports),
                    "instances": minimal_reports,
                }
                (run_dir / SUMMARY_JSON_FILENAME).write_text(
                    json.dumps(summary, indent=2), encoding="utf-8"
                )

    @staticmethod
    def build_fallback_summary_dict(
        run_id: str,
        guarded: bool,
        instance_ids: list[str],
        effective_model_name: str,
    ) -> dict[str, Any]:
        """In-memory minimal summary (for tests / tooling)."""
        minimal_reports = [
            {
                "instance_id": iid,
                "run_id": run_id,
                "guarded": guarded,
                "model_name": effective_model_name or "",
                "prompt_tokens": 0,
                "completion_tokens": 0,
                "iterations": 0,
                "tool_calls": 0,
                "wall_clock_s": 0.0,
                "replay_s": 0.0,
                "proof_s": 0.0,
            }
            for iid in instance_ids
        ]
        return {
            "run_id": run_id,
            "guarded": guarded,
            "n_instances": len(minimal_reports),
            "instances": minimal_reports,
        }
