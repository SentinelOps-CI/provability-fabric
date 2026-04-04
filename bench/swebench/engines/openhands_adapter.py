# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# OpenHands Engine adapter (library solve behind Engine ABC).

from __future__ import annotations

from pathlib import Path
from typing import Any, Optional

try:
    from .base import Engine
    from .openhands_engine import solve as openhands_solve
    from .direct_agent_engine import solve as direct_agent_solve
except ImportError:
    from engines.base import Engine  # type: ignore[no-redef]
    from engines.openhands_engine import solve as openhands_solve  # type: ignore[no-redef]
    from engines.direct_agent_engine import solve as direct_agent_solve  # type: ignore[no-redef]


class OpenHandsEngine(Engine):
    """Delegates to openhands_engine.solve (same contract as runner)."""

    name = "openhands"

    def solve(
        self,
        workspace_path: Optional[Path] = None,
        task_text: str = "",
        *,
        config: Any = None,
        extra_env: Optional[dict[str, str]] = None,
    ) -> Any:
        if workspace_path is None:
            raise RuntimeError("OpenHandsEngine requires workspace_path")
        return openhands_solve(
            workspace_path,
            task_text,
            config=config,
            extra_env=extra_env,
        )


class DirectAgentEngine(Engine):
    """Delegates to direct_agent_engine.solve."""

    name = "direct_agent"

    def solve(
        self,
        workspace_path: Optional[Path] = None,
        task_text: str = "",
        *,
        config: Any = None,
        extra_env: Optional[dict[str, str]] = None,
    ) -> Any:
        if workspace_path is None:
            raise RuntimeError("DirectAgentEngine requires workspace_path")
        return direct_agent_solve(
            workspace_path,
            task_text,
            config=config,
            extra_env=extra_env,
        )


def get_engine(engine_name: str) -> Engine:
    """Factory for supported engine names."""
    if engine_name == "mock":
        try:
            from .mock_engine import MockEngine
        except ImportError:
            from engines.mock_engine import MockEngine  # type: ignore[no-redef]

        return MockEngine()
    if engine_name == "openhands":
        return OpenHandsEngine()
    if engine_name == "direct_agent":
        return DirectAgentEngine()
    raise ValueError("Unknown engine: %s" % engine_name)
