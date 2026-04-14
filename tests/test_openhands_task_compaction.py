# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import tempfile
from pathlib import Path


def test_compact_task_preserves_reminder_and_writes_sidecar() -> None:
    from bench.swebench.engines import openhands_engine

    # Construct a prompt that matches bench/swebench/workspace.py markers.
    instruction = "# Task: GitHub issue — implement the fix in code\n**Leave your edits in place when done.**\n"
    problem = "A" * 3000
    reminder = (
        "\n**Reminder:** Implement the fix by editing files (use edit_file / file_editor). "
        "Output code edits, not only a suggestion to open an issue.\n"
    )
    efficiency = "\n**Efficiency:** Prefer applying the minimal code fix first.\n"
    task = instruction + problem + reminder + efficiency

    with tempfile.TemporaryDirectory() as td:
        scratch_dir = Path(td)
        effective, report = openhands_engine._compact_task_text_for_openhands(  # noqa: SLF001
            task_text=task,
            scratch_dir=scratch_dir,
            max_task_chars=800,
        )

        assert len(effective) <= 800
        assert "**Reminder:**" in effective
        assert "compaction_applied" in report
        assert report["compaction_applied"] is True
        assert report["critical_drop"] is False

        sidecar = scratch_dir / "pf_task_full.md"
        assert sidecar.exists()
        saved = sidecar.read_text(encoding="utf-8", errors="replace")
        assert saved == task

