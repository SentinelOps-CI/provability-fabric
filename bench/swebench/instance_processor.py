# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Per-instance orchestration hooks (workspace + engine); runner keeps the full loop.

from __future__ import annotations

from pathlib import Path
from typing import Any, Callable, Optional, Tuple

try:
    from .loader import SWEbenchInstance
    from .workspace import WorkspaceManifest
    from .workspace_manager import WorkspaceManager
except ImportError:
    from loader import SWEbenchInstance  # type: ignore[no-redef]
    from workspace import WorkspaceManifest  # type: ignore[no-redef]
    from workspace_manager import WorkspaceManager  # type: ignore[no-redef]

# (model_patch, log_text, engine_trace)
EngineRunFn = Callable[..., Tuple[str, str, Optional[dict]]]


class InstanceProcessor:
    """Thin facade: materialize workspace and invoke the configured engine."""

    def __init__(
        self,
        workspace_manager: WorkspaceManager,
        run_engine_fn: Optional[EngineRunFn] = None,
    ):
        self._workspace = workspace_manager
        self._run_engine = run_engine_fn

    def materialize_workspace(self, instance: SWEbenchInstance) -> tuple[Path, WorkspaceManifest, str]:
        return self._workspace.materialize(instance)

    def run_engine(
        self,
        instance_dict: dict,
        engine: str,
        run_dir: Path,
        instance_id: str,
        *,
        workspace_path: Optional[Path] = None,
        task_text: Optional[str] = None,
        openhands_config: Optional[Any] = None,
        openhands_extra_env: Optional[dict] = None,
    ) -> tuple[str, str, Optional[dict]]:
        if self._run_engine is None:
            raise RuntimeError("run_engine_fn not configured")
        return self._run_engine(
            instance_dict,
            engine,
            run_dir,
            instance_id,
            workspace_path=workspace_path,
            task_text=task_text,
            openhands_config=openhands_config,
            openhands_extra_env=openhands_extra_env,
        )
