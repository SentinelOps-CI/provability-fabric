# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Workspace manager for SWE-bench: encapsulates workspace materialization and lifecycle.

from __future__ import annotations

from pathlib import Path
from typing import Optional

try:
    from .loader import SWEbenchInstance
    from .util import sanitize_instance_id
    from .workspace import WorkspaceManifest, materialize_workspace as _materialize_workspace
except ImportError:  # script-style execution from bench/swebench/
    from loader import SWEbenchInstance  # type: ignore[no-redef]
    from util import sanitize_instance_id  # type: ignore[no-redef]
    from workspace import WorkspaceManifest, materialize_workspace as _materialize_workspace  # type: ignore[no-redef]


class WorkspaceManager:
    """Manages workspace lifecycle for SWE-bench instances."""

    def __init__(self, workspaces_dir: str | Path = "workspaces", force_refresh: bool = False):
        self.workspaces_dir = Path(workspaces_dir)
        self.force_refresh = force_refresh

    def materialize(self, instance: SWEbenchInstance) -> tuple[Path, WorkspaceManifest, str]:
        """Materialize workspace; returns (workspace_root, manifest, manifest_sha256)."""
        return _materialize_workspace(
            instance,
            workspaces_dir=self.workspaces_dir,
            force_refresh=self.force_refresh,
        )

    def get_workspace_path(self, instance_id: str) -> Path:
        """Predicted workspace root for instance_id (same layout as materialize_workspace)."""
        sid = sanitize_instance_id(instance_id)
        return (self.workspaces_dir / sid).resolve()

    def cleanup(self, workspace_path: Path) -> None:
        """Optional hook for future teardown; workspaces are reused by default."""
        del workspace_path  # noqa: ARG002
