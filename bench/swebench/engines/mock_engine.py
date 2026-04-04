# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Mock engine for CI smoke tests: no OpenHands dependency. Deterministic and fast.
# Writes 2-3 tool calls into the trace; in guarded mode runs one denied command (curl)
# so the guard writes exactly one violation event (reason_code=binary_forbidden).

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional

try:
    from .openhands_engine import EngineTrace, SolveResult
except ImportError:
    EngineTrace = None  # type: ignore[misc, assignment]
    SolveResult = None  # type: ignore[misc, assignment]

# When guarded, we expect exactly one violation with this reason (guard uses binary_forbidden for curl).
EXPECTED_VIOLATION_REASON_CODE = "binary_forbidden"

# Static minimal diff when no workspace (--no-workspace).
STATIC_MOCK_DIFF = """diff --git a/.pf_mock_smoke b/.pf_mock_smoke
new file mode 100644
index 0000000..e69de29
--- /dev/null
+++ b/.pf_mock_smoke
"""


def _run_via_shell(command: str, extra_env: Optional[Dict[str, str]] = None, cwd: Optional[Path] = None) -> Dict[str, Any]:
    """Run a single command via SHELL (guard when guarded). Returns dict for tool_calls trace."""
    env = dict(os.environ)
    if extra_env:
        env.update(extra_env)
    shell = env.get("SHELL", "bash")
    try:
        r = subprocess.run(
            [shell, "-c", command],
            env=env,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=10,
            encoding="utf-8",
            errors="replace",
        )
        return {
            "command": command,
            "allowed": True,
            "exit_code": r.returncode,
            "stdout": (r.stdout or "")[:500],
            "stderr": (r.stderr or "")[:500],
        }
    except subprocess.TimeoutExpired:
        return {"command": command, "allowed": True, "exit_code": -1, "timeout": True}
    except Exception as e:
        return {"command": command, "allowed": True, "exit_code": -1, "error": str(e)[:200]}


def _get_mock_patch_with_workspace(workspace_path: Path) -> str:
    """Produce a minimal valid diff by touching a file in workspace/repo and running git diff HEAD."""
    repo_dir = workspace_path / "repo"
    if not repo_dir.is_dir():
        return STATIC_MOCK_DIFF
    dummy = repo_dir / ".pf_mock_smoke"
    try:
        dummy.write_text("mock smoke\n", encoding="utf-8")
        out = subprocess.run(
            ["git", "diff", "HEAD"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=5,
        )
        patch_str = (out.stdout or "").strip()
        if patch_str:
            return patch_str
    except (OSError, subprocess.TimeoutExpired, subprocess.CalledProcessError):
        pass
    finally:
        try:
            if dummy.exists():
                dummy.unlink()
        except OSError:
            pass
    return STATIC_MOCK_DIFF


def solve(
    workspace_path: Optional[str | Path] = None,
    task_text: Optional[str] = None,
    config: Any = None,
    extra_env: Optional[Dict[str, str]] = None,
) -> SolveResult:
    """
    Mock solver: deterministic, no model. Runs 2-3 tool calls; in guarded mode
    one is denied (curl) so the guard writes exactly one violation event.
    Returns SolveResult(success=True, patch_diff_str=..., trace=...).
    """
    if SolveResult is None or EngineTrace is None:
        raise RuntimeError("mock_engine requires openhands_engine (SolveResult, EngineTrace)")

    tool_calls: List[Dict[str, Any]] = []
    guarded = bool(extra_env and extra_env.get("SHELL") and "guard" in str(extra_env.get("SHELL", "")).lower())
    cwd = None
    if workspace_path:
        wp = Path(workspace_path)
        if wp.is_dir():
            repo = wp / "repo"
            cwd = repo if repo.is_dir() else wp

    # 1) Allowed command
    t1 = _run_via_shell("echo ok", extra_env=extra_env, cwd=cwd)
    tool_calls.append(t1)

    # 2) Denied command only when guarded (curl -> binary_forbidden)
    if guarded:
        t2 = _run_via_shell("curl example.com", extra_env=extra_env, cwd=cwd)
        t2["allowed"] = t2.get("exit_code") == 125  # Guard uses 125 for forbidden
        tool_calls.append(t2)
        # Guard writes exactly one violation event to evidence/events.jsonl

    # Build trace
    trace = EngineTrace(
        prompts_sent=[],
        tool_calls=tool_calls,
        files_modified=[".pf_mock_smoke"] if workspace_path else [],
        raw_events=[],
    )

    # Patch: minimal valid diff
    if workspace_path and Path(workspace_path).is_dir():
        patch_diff_str = _get_mock_patch_with_workspace(Path(workspace_path))
    else:
        patch_diff_str = STATIC_MOCK_DIFF

    return SolveResult(
        patch_diff_str=patch_diff_str,
        trace=trace,
        success=True,
        error=None,
    )


try:
    from .base import Engine
except ImportError:
    try:
        from engines.base import Engine  # type: ignore[no-redef]
    except ImportError:
        Engine = object  # type: ignore[misc, assignment]


class MockEngine(Engine):  # type: ignore[misc, valid-type]
    """Adapter: mock_engine.solve behind the Engine interface (tests / future wiring)."""

    name = "mock"

    def solve(
        self,
        workspace_path: Optional[Path] = None,
        task_text: str = "",
        *,
        config: Any = None,
        extra_env: Optional[Dict[str, str]] = None,
    ) -> Any:
        return solve(
            workspace_path=workspace_path,
            task_text=task_text or None,
            config=config,
            extra_env=extra_env,
        )
