# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Facade over bench.swebench.cost_report for dependency injection and tests.

from __future__ import annotations

from pathlib import Path
from typing import Any, Callable, Optional


class CostReporter:
    """Builds and writes per-instance cost_report.json records."""

    def __init__(
        self,
        build_cost_report: Optional[Callable[..., dict]] = None,
        write_cost_report: Optional[Callable[[Path, dict], None]] = None,
    ):
        self._build = build_cost_report
        self._write = write_cost_report

    def build_report(self, **kwargs: Any) -> dict:
        if self._build is None:
            raise RuntimeError("build_cost_report not configured")
        return self._build(**kwargs)

    def write_report(self, instance_dir: Path, report: dict) -> None:
        if self._write is None:
            raise RuntimeError("write_cost_report not configured")
        self._write(Path(instance_dir), report)

    @staticmethod
    def aggregate_token_totals(reports: list[dict]) -> dict[str, int]:
        """Sum prompt/completion tokens across instance reports."""
        pt = sum(int(r.get("prompt_tokens") or 0) for r in reports)
        ct = sum(int(r.get("completion_tokens") or 0) for r in reports)
        return {"prompt_tokens_total": pt, "completion_tokens_total": ct}
