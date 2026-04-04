# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Workspace materialization for SWE-bench: checkout repo at base commit,
# write task prompt (issue + constraints), create scratch dir. Deterministic
# and idempotent; workspace manifest JSON is written and hashed for PF evidence.

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

try:
    from .loader import SWEbenchInstance
except ImportError:
    from loader import SWEbenchInstance

# Default base directory for all workspaces (override via WORKSPACES_DIR or parameter).
DEFAULT_WORKSPACES_DIR = "workspaces"


def _sanitize_instance_id(instance_id: str) -> str:
    """Filesystem-safe directory name from instance_id."""
    return "".join(c if c.isalnum() or c in "-_" else "_" for c in instance_id)


def _repo_to_clone_url(repo: str) -> str:
    """Convert dataset repo field (owner/name) to HTTPS clone URL."""
    repo = repo.strip()
    if not repo:
        return ""
    if repo.startswith(("https://", "git@")):
        return repo
    return f"https://github.com/{repo}.git"


@dataclass
class WorkspaceManifest:
    """Canonical workspace manifest for hashing and evidence."""

    instance_id: str
    repo: str
    base_commit: str
    workspace_root: str
    repo_path: str
    task_prompt_path: str
    scratch_path: str
    resolved_commit: str = ""
    manifest_version: str = "1"

    def to_canonical_dict(self) -> dict:
        """Ordered, deterministic dict for hashing (no extra keys)."""
        return {
            "manifest_version": self.manifest_version,
            "instance_id": self.instance_id,
            "repo": self.repo,
            "base_commit": self.base_commit,
            "workspace_root": str(Path(self.workspace_root).resolve()),
            "repo_path": str(Path(self.repo_path).resolve()),
            "task_prompt_path": str(Path(self.task_prompt_path).resolve()),
            "scratch_path": str(Path(self.scratch_path).resolve()),
            "resolved_commit": self.resolved_commit,
        }

    def to_json_canonical(self) -> str:
        """Canonical JSON string (sorted keys, no trailing whitespace) for hashing."""
        return json.dumps(self.to_canonical_dict(), sort_keys=True, separators=(",", ":"))

    def sha256(self) -> str:
        return hashlib.sha256(self.to_json_canonical().encode("utf-8")).hexdigest()


def _run_git(cwd: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git"] + list(args),
        cwd=cwd,
        capture_output=True,
        text=True,
        check=check,
    )


def _get_head_commit(repo_path: Path) -> str:
    try:
        p = _run_git(repo_path, "rev-parse", "HEAD")
        return (p.stdout or "").strip()[:40]
    except (subprocess.CalledProcessError, FileNotFoundError):
        return ""


def materialize_workspace(
    instance: SWEbenchInstance,
    workspaces_dir: str | Path = DEFAULT_WORKSPACES_DIR,
    force_refresh: bool = False,
) -> tuple[Path, WorkspaceManifest, str]:
    """
    Create an isolated workspace for the given instance: checkout repo at base commit,
    write task prompt (issue + constraints), create scratch dir. Idempotent and
    deterministic for the same instance_id.

    Returns:
        (workspace_root, manifest, manifest_sha256)
    """
    workspaces_dir = Path(workspaces_dir)
    sid = _sanitize_instance_id(instance.instance_id)
    workspace_root = workspaces_dir / sid
    repo_path = workspace_root / "repo"
    task_prompt_path = workspace_root / "task_prompt.md"
    scratch_path = workspace_root / "scratch"

    manifest_path = workspace_root / "workspace_manifest.json"
    existing_manifest: Optional[WorkspaceManifest] = None
    if manifest_path.exists() and not force_refresh:
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
            existing_manifest = WorkspaceManifest(
                instance_id=data["instance_id"],
                repo=data["repo"],
                base_commit=data["base_commit"],
                workspace_root=str(workspace_root),
                repo_path=str(repo_path),
                task_prompt_path=str(task_prompt_path),
                scratch_path=str(scratch_path),
                resolved_commit=data.get("resolved_commit", ""),
                manifest_version=data.get("manifest_version", "1"),
            )
            if (
                existing_manifest.base_commit == instance.base_commit
                and existing_manifest.instance_id == instance.instance_id
            ):
                repo_path_resolved = Path(repo_path)
                if repo_path_resolved.exists() and (repo_path_resolved / ".git").exists():
                    scratch_path.mkdir(parents=True, exist_ok=True)
                    # Ensure clean working tree so each run starts from base_commit (prevents
                    # huge diffs from a previous run's leftover changes).
                    try:
                        _run_git(repo_path_resolved, "checkout", instance.base_commit, check=False)
                        _run_git(repo_path_resolved, "reset", "--hard", "HEAD", check=False)
                        _run_git(repo_path_resolved, "clean", "-fd", check=False)
                    except Exception:
                        pass
                    manifest = WorkspaceManifest(
                        instance_id=instance.instance_id,
                        repo=instance.repo,
                        base_commit=instance.base_commit,
                        workspace_root=str(workspace_root.resolve()),
                        repo_path=str(repo_path.resolve()),
                        task_prompt_path=str(task_prompt_path.resolve()),
                        scratch_path=str(scratch_path.resolve()),
                        resolved_commit=_get_head_commit(repo_path_resolved)
                        or existing_manifest.resolved_commit,
                        manifest_version="1",
                    )
                    h = manifest.sha256()
                    _write_manifest_and_hash(workspace_root, manifest, h)
                    return workspace_root.resolve(), manifest, h
        except (json.JSONDecodeError, KeyError):
            pass

    workspace_root.mkdir(parents=True, exist_ok=True)
    clone_url = _repo_to_clone_url(instance.repo)
    if not clone_url:
        raise ValueError(f"Invalid repo for instance {instance.instance_id}: {instance.repo!r}")

    if not repo_path.exists() or not (repo_path / ".git").exists():
        _run_git(workspace_root, "clone", "--no-checkout", clone_url, "repo")
    else:
        try:
            _run_git(repo_path, "fetch", "origin", instance.base_commit, check=False)
        except Exception:
            pass

    _run_git(repo_path, "checkout", instance.base_commit)
    resolved = _get_head_commit(repo_path)

    task_content = _build_task_prompt(instance)
    task_prompt_path.write_text(task_content, encoding="utf-8")
    scratch_path.mkdir(parents=True, exist_ok=True)

    manifest = WorkspaceManifest(
        instance_id=instance.instance_id,
        repo=instance.repo,
        base_commit=instance.base_commit,
        workspace_root=str(workspace_root.resolve()),
        repo_path=str(repo_path.resolve()),
        task_prompt_path=str(task_prompt_path.resolve()),
        scratch_path=str(scratch_path.resolve()),
        resolved_commit=resolved,
        manifest_version="1",
    )
    h = manifest.sha256()
    _write_manifest_and_hash(workspace_root, manifest, h)
    return workspace_root.resolve(), manifest, h


def _build_task_prompt(instance: SWEbenchInstance) -> str:
    """Issue text plus constraints (hints) as a single task prompt file.
    Prefix instructs the agent to implement the fix by editing files (SWE-bench expects a patch).
    Explicit tool instruction (file_editor/edit_file) improves headless tool use when skills inject extra prompt text.
    """
    instruction = (
        "# Task: GitHub issue — implement the fix in code\n"
        "**You must implement the fix by editing the repository files.** "
        "Do not only discuss, suggest, or offer to file an issue; produce concrete code changes. "
        "Use the file_editor or edit_file tool (or run_terminal_cmd if needed) to apply your changes. "
        "Your edits will be evaluated as a patch. "
        "Do not respond with only a suggestion to create a GitHub issue; you must make the code changes yourself.\n"
        "**Leave your edits in place when done.** Do not run git checkout, git restore, git reset --hard, or any command that reverts or undoes your code changes. The working tree must still contain your edits when you finish.\n\n"
    )
    parts = [instruction, instance.problem_statement.strip(), "\n"]
    if (instance.hints_text or "").strip():
        parts.append("\n# Constraints / Hints\n")
        parts.append(instance.hints_text.strip())
        parts.append("\n")
    parts.append(
        "\n**Reminder:** Implement the fix by editing files (use edit_file / file_editor). Output code edits, not only a suggestion to open an issue. Do not revert your edits (no git checkout/restore/reset that would remove your changes).\n"
    )
    parts.append(
        "\n**Efficiency:** Prefer applying the minimal code fix first. Do not spend most of the budget installing packages or running a full test suite unless a quick local check is enough to validate your edit; if the environment is slow, still leave correct edits in the working tree.\n"
    )
    return "".join(parts)


GUARDED_SHELL_APPENDIX = (
    "\n\n## PF-guarded shell (this run only)\n"
    "Network access from the shell is disabled (no curl, wget, or pip against URLs).\n"
    "If a terminal command fails with exit code **125** or stderr contains **DENIED**, do not repeat that command; "
    "use a permitted alternative (e.g. `pip install -e .` from the repo root without URLs, `python -m pytest` on a single file, or skip tests and finish the code change).\n"
    "Temporary files for subprocesses use the workspace scratch directory.\n"
)


def _write_manifest_and_hash(workspace_root: Path, manifest: WorkspaceManifest, sha256_hex: str) -> None:
    """Write workspace_manifest.json and workspace_manifest_sha256.txt."""
    out = manifest.to_canonical_dict()
    out["workspace_manifest_sha256"] = sha256_hex
    (workspace_root / "workspace_manifest.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8"
    )
    (workspace_root / "workspace_manifest_sha256.txt").write_text(sha256_hex + "\n", encoding="utf-8")
