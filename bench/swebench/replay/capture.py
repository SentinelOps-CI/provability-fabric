# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Capture: records all tool I/O needed to replay an agent run.
# Produces a replay bundle (replay_bundle.json) with tool trace and
# file edits so replay can reconstitute the patch without calling the model.
# See docs/Replay.md and PF TRACE-REPLAY-KIT posture.

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from bench.swebench.constants import REPLAY_BUNDLE_FILENAME

BUNDLE_VERSION = "1"


def _sha256_hex(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def build_replay_bundle(
    instance_dir: Path,
    repo_path: Optional[Path] = None,
    engine_trace_dict: Optional[dict] = None,
    model_patch: Optional[str] = None,
) -> dict:
    """
    Build a replay bundle from an instance evidence dir (and optional live repo).

    Reads engine_trace.json and model.patch from instance_dir if not provided.
    If repo_path is given, reads final content of each file in files_modified
    so replay can reconstitute the patch by applying file_edits.

    Returns a dict suitable for replay_bundle.json:
      - instance_id, run_id (from metadata if present)
      - original_patch_sha256
      - tool_trace: list of { tool, args } from engine_trace
      - file_edits: list of { path, content } (only when repo_path was provided)
    """
    instance_dir = Path(instance_dir)
    bundle: Dict[str, Any] = {
        "version": BUNDLE_VERSION,
        "original_patch_sha256": "",
        "tool_trace": [],
        "file_edits": [],
    }

    # Load metadata for instance_id / run_id
    meta_path = instance_dir / "metadata.json"
    if meta_path.exists():
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
            bundle["instance_id"] = meta.get("instance_id", "")
        except (json.JSONDecodeError, OSError):
            bundle["instance_id"] = ""
    else:
        bundle["instance_id"] = ""

    # Load engine trace
    trace = engine_trace_dict
    if trace is None:
        trace_path = instance_dir / "engine_trace.json"
        if trace_path.exists():
            try:
                trace = json.loads(trace_path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, OSError):
                trace = {}
    if not isinstance(trace, dict):
        trace = {}

    bundle["tool_trace"] = list(trace.get("tool_calls") or [])
    files_modified: List[str] = list(trace.get("files_modified") or [])

    # Load model patch and compute hash
    patch_str = model_patch
    if patch_str is None:
        patch_path = instance_dir / "model.patch"
        if patch_path.exists():
            patch_str = patch_path.read_text(encoding="utf-8")
        else:
            patch_str = ""
    bundle["original_patch_sha256"] = _sha256_hex(patch_str)

    # If we have a repo path, capture final content of each modified file
    if repo_path is not None:
        repo_path = Path(repo_path).resolve()
        if repo_path.is_dir():
            for rel_path in files_modified:
                if not rel_path or ".." in rel_path:
                    continue
                full = repo_path / rel_path
                try:
                    if full.is_file():
                        content = full.read_text(encoding="utf-8", errors="replace")
                        bundle["file_edits"].append({"path": rel_path, "content": content})
                except OSError:
                    pass

    return bundle


def write_replay_bundle(instance_dir: Path, bundle: dict) -> Path:
    """Write replay_bundle.json into instance_dir. Returns path to written file."""
    instance_dir = Path(instance_dir)
    instance_dir.mkdir(parents=True, exist_ok=True)
    out_path = instance_dir / REPLAY_BUNDLE_FILENAME
    out_path.write_text(json.dumps(bundle, indent=2), encoding="utf-8")
    return out_path
