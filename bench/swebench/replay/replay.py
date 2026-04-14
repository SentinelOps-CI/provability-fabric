# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Replay: deterministically replay an agent run without calling the model.
# Applies captured tool I/O (file_edits), reconstitutes the patch via git diff,
# and verifies the patch hash matches the original. See docs/Replay.md.

from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, List, Optional, Tuple

from bench.swebench.constants import REPLAY_BUNDLE_FILENAME


@dataclass
class ReplayResult:
    """Result of replaying one instance."""

    instance_id: str
    success: bool
    original_patch_sha256: str
    reconstituted_patch_sha256: str
    match: bool
    message: str
    repo_path: Optional[str] = None


def _sha256_hex(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _run_git(repo_path: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git"] + list(args),
        cwd=repo_path,
        capture_output=True,
        text=True,
        check=check,
        timeout=60,
    )


def _get_repo_at_base(repo_path: Path, base_commit: str) -> bool:
    """Checkout base commit and clean working tree. Returns True on success."""
    try:
        _run_git(repo_path, "checkout", "--force", base_commit)
        _run_git(repo_path, "clean", "-fd", check=False)
        _run_git(repo_path, "reset", "--hard", "HEAD")
        return True
    except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
        return False


def _get_patch_from_repo(repo_path: Path) -> str:
    """Return git diff HEAD (unstaged + staged) as string."""
    try:
        out = _run_git(repo_path, "diff", "HEAD")
        return out.stdout or ""
    except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
        return ""


def _load_replay_bundle(instance_dir: Path) -> Optional[dict]:
    """Load replay_bundle.json; if missing, build from engine_trace + model.patch."""
    bundle_path = instance_dir / REPLAY_BUNDLE_FILENAME
    if bundle_path.exists():
        try:
            return json.loads(bundle_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            pass
    # Fallback: build minimal bundle from existing evidence
    try:
        from .capture import build_replay_bundle
        return build_replay_bundle(instance_dir, repo_path=None)
    except Exception:
        pass
    return None


def _load_workspace_manifest(instance_dir: Path) -> Optional[dict]:
    """Load workspace_manifest.json if present."""
    path = instance_dir / "workspace_manifest.json"
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def replay_instance(
    instance_dir: Path,
    repo_path: Optional[Path] = None,
    base_commit: Optional[str] = None,
    workspaces_dir: Optional[Path] = None,
) -> ReplayResult:
    """
    Replay one instance: apply file_edits from replay bundle, reconstitute patch, compare hash.

    If repo_path is None, derives it from instance_dir/workspace_manifest.json (workspace_root/repo).
    If base_commit is None, uses workspace_manifest base_commit.
    """
    instance_dir = Path(instance_dir)
    bundle = _load_replay_bundle(instance_dir)
    if not bundle:
        return ReplayResult(
            instance_id=instance_dir.name,
            success=False,
            original_patch_sha256="",
            reconstituted_patch_sha256="",
            match=False,
            message="No replay bundle and could not build from evidence",
        )

    instance_id = bundle.get("instance_id") or instance_dir.name
    original_hash = bundle.get("original_patch_sha256") or ""
    file_edits = bundle.get("file_edits") or []
    tool_trace = bundle.get("tool_trace") or []

    if not original_hash:
        return ReplayResult(
            instance_id=instance_id,
            success=False,
            original_patch_sha256="",
            reconstituted_patch_sha256="",
            match=False,
            message="Bundle missing original_patch_sha256",
        )

    # Resolve repo path
    repo: Optional[Path] = Path(repo_path).resolve() if repo_path else None
    base: Optional[str] = base_commit
    if repo is None:
        manifest = _load_workspace_manifest(instance_dir)
        if manifest:
            repo_path_str = manifest.get("repo_path")
            base = base or manifest.get("base_commit")
            if repo_path_str:
                repo = Path(repo_path_str).resolve()
        if repo is None and workspaces_dir:
            # workspace_root in manifest is workspaces_dir / sanitized_instance_id
            if manifest:
                ws_root = manifest.get("workspace_root")
                if ws_root:
                    repo = Path(ws_root) / "repo"
                    if not repo.is_dir():
                        repo = None

    if repo is None or not repo.is_dir():
        return ReplayResult(
            instance_id=instance_id,
            success=False,
            original_patch_sha256=original_hash,
            reconstituted_patch_sha256="",
            match=False,
            message="Repo path not found (workspace_manifest or --workspace)",
            repo_path=str(repo) if repo else None,
        )

    if base:
        if not _get_repo_at_base(repo, base):
            return ReplayResult(
                instance_id=instance_id,
                success=False,
                original_patch_sha256=original_hash,
                reconstituted_patch_sha256="",
                match=False,
                message=f"Failed to checkout base commit {base}",
                repo_path=str(repo),
            )

    # Apply file_edits in order (deterministic)
    for edit in file_edits:
        path_key = edit.get("path")
        content = edit.get("content", "")
        if not path_key or ".." in path_key:
            continue
        target = repo / path_key
        try:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
        except OSError as e:
            return ReplayResult(
                instance_id=instance_id,
                success=False,
                original_patch_sha256=original_hash,
                reconstituted_patch_sha256="",
                match=False,
                message=f"Failed to write {path_key}: {e}",
                repo_path=str(repo),
            )

    # Reconstitute patch and compare hash
    reconstituted = _get_patch_from_repo(repo)
    reconstituted_hash = _sha256_hex(reconstituted)
    match = reconstituted_hash == original_hash

    return ReplayResult(
        instance_id=instance_id,
        success=True,
        original_patch_sha256=original_hash,
        reconstituted_patch_sha256=reconstituted_hash,
        match=match,
        message="Match" if match else "Patch hash mismatch",
        repo_path=str(repo),
    )


def replay_run(
    run_dir: Path,
    instance_id_filter: Optional[Any] = None,
    repo_path_resolver: Optional[Callable[[str, dict], Optional[Tuple[Optional[Path], Optional[str]]]]] = None,
    workspaces_dir: Optional[Path] = None,
) -> Tuple[List[ReplayResult], bool]:
    """
    Replay all instances in a run dir (or a subset if instance_id_filter is set).

    instance_id_filter: optional str (single) or list of str (multiple); dir name must match.
    repo_path_resolver(instance_id, manifest) -> (repo_path, base_commit) or None.
    Returns (list of ReplayResult, all_matched).
    """
    run_dir = Path(run_dir)
    if not run_dir.is_dir():
        return [], False

    allow_set = None
    if instance_id_filter is not None:
        allow_set = {instance_id_filter} if isinstance(instance_id_filter, str) else set(instance_id_filter)

    results: List[ReplayResult] = []
    for child in sorted(run_dir.iterdir()):
        if not child.is_dir():
            continue
        if allow_set is not None and child.name not in allow_set:
            continue
        meta = child / "metadata.json"
        if not meta.exists():
            continue
        manifest = _load_workspace_manifest(child)
        repo_path = base_commit = None
        if repo_path_resolver and manifest:
            resolved = repo_path_resolver(
                manifest.get("instance_id", child.name),
                manifest,
            )
            if resolved:
                repo_path, base_commit = resolved
        if repo_path is None and manifest:
            rp = manifest.get("repo_path")
            if rp:
                repo_path = Path(rp)
            base_commit = base_commit or manifest.get("base_commit")

        r = replay_instance(
            child,
            repo_path=repo_path,
            base_commit=base_commit,
            workspaces_dir=workspaces_dir,
        )
        results.append(r)

    all_matched = bool(results) and all(r.match for r in results)
    return results, all_matched
