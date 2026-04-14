# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# PF evidence bundle writer (one instance directory under runs/<run_id>/).

from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

try:
    from .util import sanitize_instance_id
except ImportError:
    from util import sanitize_instance_id  # type: ignore[no-redef]


@dataclass
class EvidenceBundle:
    """Structured inputs for a single-instance evidence bundle."""

    instance_id: str
    model_patch: str
    log_text: str
    workspace_manifest_sha256: Optional[str] = None
    workspace_manifest_dict: Optional[dict] = None
    engine_trace_dict: Optional[dict] = None
    policy_name: Optional[str] = None
    policy_hash: Optional[str] = None
    engine_mode: Optional[str] = None
    engine_success: Optional[bool] = None
    engine_error: Optional[str] = None


class EvidenceWriter:
    """Writes run.log, patches, metadata, workspace manifest, and engine trace for one instance."""

    def __init__(self, run_dir: Path):
        self.run_dir = Path(run_dir)

    def write_bundle(self, bundle: EvidenceBundle) -> None:
        write_instance_evidence(
            self.run_dir,
            bundle.instance_id,
            bundle.model_patch,
            bundle.log_text,
            workspace_manifest_sha256=bundle.workspace_manifest_sha256,
            workspace_manifest_dict=bundle.workspace_manifest_dict,
            engine_trace_dict=bundle.engine_trace_dict,
            policy_name=bundle.policy_name,
            policy_hash=bundle.policy_hash,
            engine_mode=bundle.engine_mode,
            engine_success=bundle.engine_success,
            engine_error=bundle.engine_error,
        )

    def write_trace(self, instance_id: str, trace: dict) -> None:
        """Write or overwrite ``engine_trace.json`` for an instance (atomic with instance dir)."""
        inst_dir = self.run_dir / sanitize_instance_id(instance_id)
        inst_dir.mkdir(parents=True, exist_ok=True)
        (inst_dir / "engine_trace.json").write_text(
            json.dumps(trace, indent=2), encoding="utf-8"
        )

    def write(
        self,
        instance_id: str,
        model_patch: str,
        log_text: str,
        *,
        workspace_manifest_sha256: Optional[str] = None,
        workspace_manifest_dict: Optional[dict] = None,
        engine_trace_dict: Optional[dict] = None,
        policy_name: Optional[str] = None,
        policy_hash: Optional[str] = None,
        engine_mode: Optional[str] = None,
        engine_success: Optional[bool] = None,
        engine_error: Optional[str] = None,
    ) -> None:
        """Same contract as legacy write_evidence for drop-in use."""
        write_instance_evidence(
            self.run_dir,
            instance_id,
            model_patch,
            log_text,
            workspace_manifest_sha256=workspace_manifest_sha256,
            workspace_manifest_dict=workspace_manifest_dict,
            engine_trace_dict=engine_trace_dict,
            policy_name=policy_name,
            policy_hash=policy_hash,
            engine_mode=engine_mode,
            engine_success=engine_success,
            engine_error=engine_error,
        )


def write_instance_evidence(
    run_dir: Path,
    instance_id: str,
    model_patch: str,
    log_text: str,
    workspace_manifest_sha256: Optional[str] = None,
    workspace_manifest_dict: Optional[dict] = None,
    engine_trace_dict: Optional[dict] = None,
    policy_name: Optional[str] = None,
    policy_hash: Optional[str] = None,
    engine_mode: Optional[str] = None,
    engine_success: Optional[bool] = None,
    engine_error: Optional[str] = None,
) -> None:
    """Write PF evidence bundle for one instance."""
    inst_dir = run_dir / sanitize_instance_id(instance_id)
    inst_dir.mkdir(parents=True, exist_ok=True)
    if workspace_manifest_sha256:
        log_text = log_text + "\nworkspace_manifest_sha256=" + workspace_manifest_sha256
    if policy_hash:
        log_text = log_text + "\npolicy_hash=" + policy_hash
    (inst_dir / "run.log").write_text(log_text, encoding="utf-8")
    (inst_dir / "model.patch").write_text(model_patch, encoding="utf-8")
    (inst_dir / "patch.diff").write_text(model_patch, encoding="utf-8")
    meta = {
        "instance_id": instance_id,
        "patch_length": len(model_patch),
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }
    if workspace_manifest_sha256:
        meta["workspace_manifest_sha256"] = workspace_manifest_sha256
    if policy_name:
        meta["policy_name"] = policy_name
    if policy_hash:
        meta["policy_hash"] = policy_hash
    if engine_mode is not None:
        meta["engine_mode"] = engine_mode
    if engine_success is not None:
        meta["engine_success"] = engine_success
    meta["engine_error"] = engine_error
    (inst_dir / "metadata.json").write_text(json.dumps(meta, indent=2), encoding="utf-8")
    if workspace_manifest_dict is not None:
        (inst_dir / "workspace_manifest.json").write_text(
            json.dumps(workspace_manifest_dict, indent=2), encoding="utf-8"
        )
    if engine_trace_dict is not None:
        (inst_dir / "engine_trace.json").write_text(
            json.dumps(engine_trace_dict, indent=2), encoding="utf-8"
        )
