# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Abstract engine interface for SWE-bench solvers (testability and future adapters).

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any, Optional


class Engine(ABC):
    """Pluggable solver: produce a patch and trace for one workspace + task."""

    name: str = "abstract"

    @abstractmethod
    def solve(
        self,
        workspace_path: Optional[Path],
        task_text: str,
        *,
        config: Optional[Any] = None,
        extra_env: Optional[dict[str, str]] = None,
    ) -> Any:
        """Return engine-specific result (typically SolveResult from openhands_engine)."""
        raise NotImplementedError
