# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Deterministic (gold-patch) engine adapter: no LLM; used when runner mode is deterministic.

from __future__ import annotations

from pathlib import Path
from typing import Any, Optional

try:
    from .base import Engine
    from .openhands_engine import EngineTrace, SolveResult
except ImportError:
    from engines.base import Engine  # type: ignore[no-redef]
    from engines.openhands_engine import EngineTrace, SolveResult  # type: ignore[no-redef]


class DeterministicEngine(Engine):
    """
    Produces a patch from a pre-specified gold diff (caller supplies via side channel).

    The SWE-bench runner implements deterministic mode inline (gold patch from instance);
    this class exists for interface completeness and tests that expect an Engine per mode.
    """

    name = "deterministic"

    def solve(
        self,
        workspace_path: Optional[Path] = None,
        task_text: str = "",
        *,
        config: Any = None,
        extra_env: Optional[dict[str, str]] = None,
    ) -> Any:
        if SolveResult is None or EngineTrace is None:
            raise RuntimeError("deterministic_engine requires openhands_engine (SolveResult, EngineTrace)")
        trace = EngineTrace(
            prompts_sent=[],
            tool_calls=[],
            files_modified=[],
            raw_events=[],
        )
        return SolveResult(
            patch_diff_str="",
            trace=trace,
            success=True,
            error=None,
        )
