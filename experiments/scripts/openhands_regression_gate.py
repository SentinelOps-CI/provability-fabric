#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Operational regression gate for OpenHands runtime + Prime/OpenAI compatibility.
#
# This script runs a single synthetic OpenHands solve and fails fast when any of the
# stabilization invariants are violated:
# - task fidelity critical-drop (prompt compaction dropped required blocks)
# - timeout occurred before first actionable step (startup latency too high)
# - metadata mismatch (execution_mode not what the configured provider expects)
# - Prime compatibility: proxy did not prevent unnormalized 422-compatible errors

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from time import perf_counter


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def _bin_exists(name: str) -> bool:
    from shutil import which

    return which(name) is not None


def _build_synthetic_workspace(workspace_root: Path) -> tuple[Path, Path]:
    repo_dir = workspace_root / "repo"
    scratch_dir = workspace_root / "scratch"
    repo_dir.mkdir(parents=True, exist_ok=True)
    scratch_dir.mkdir(parents=True, exist_ok=True)

    subprocess.run(["git", "init"], cwd=str(repo_dir), check=True, capture_output=True, text=True)
    (repo_dir / "hello.py").write_text("def hello():\n    return 'hello'\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=str(repo_dir), check=True, capture_output=True, text=True)
    subprocess.run(
        ["git", "-c", "user.name=pf", "-c", "user.email=pf@example.com", "commit", "-m", "init"],
        cwd=str(repo_dir),
        check=True,
        capture_output=True,
        text=True,
    )
    return repo_dir, scratch_dir


def _build_long_swebench_task_text() -> str:
    # Force a compaction path by including critical markers and a large problem section.
    instruction = (
        "# Task: GitHub issue — implement the fix in code\n"
        "**You must implement the fix by editing the repository files.** "
        "Use edit_file / file_editor to apply changes.\n"
        "**Leave your edits in place when done.** Do not revert changes.\n\n"
    )
    # Put the constraints marker near the end so tail-preservation keeps it.
    problem = "PROBLEM " * 4000
    constraints = (
        "# Constraints / Hints\n"
        "- Edit hello.py and make hello() return 'ok'.\n"
        "- Avoid unnecessary refactors.\n"
        "\n"
    )
    reminder = (
        "**Reminder:** Implement the fix by editing files (use edit_file / file_editor). "
        "Output code edits, not only a suggestion to open an issue.\n"
    )
    efficiency = (
        "**Efficiency:** Prefer applying the minimal code fix first. Keep changes small.\n"
    )
    return instruction + problem + "\n\n" + constraints + "\n" + "\n" + reminder + "\n" + "\n" + efficiency + "\n"


def _compute_expected_execution_mode(provider_normalized: str, openhands_library_core_available: bool) -> str:
    if provider_normalized == "prime_intellect":
        return "prime_subprocess"
    return "library" if openhands_library_core_available else "cli_subprocess"


def main() -> int:
    parser = argparse.ArgumentParser(description="1-instance OpenHands regression gate.")
    parser.add_argument("--provider", type=str, default=os.environ.get("OPENHANDS_PROVIDER", "openai"))
    parser.add_argument("--model", type=str, default=os.environ.get("OPENHANDS_MODEL", "gpt-4o-mini"))
    parser.add_argument("--timeout", type=int, default=int(os.environ.get("OPENHANDS_GATE_TIMEOUT_S", "180")))
    parser.add_argument("--max-iterations", type=int, default=int(os.environ.get("OPENHANDS_GATE_MAX_ITERATIONS", "2")))
    # Default high enough for the gate's long synthetic SWE-bench-shaped prompt; the bench runner
    # may use a lower PF_OPENHANDS_MAX_TASK_CHARS for tmux safety — do not inherit 500 here.
    parser.add_argument(
        "--max-task-chars",
        type=int,
        default=int(os.environ.get("PF_OPENHANDS_MAX_TASK_CHARS", "12000")),
    )
    args = parser.parse_args()

    if not _bin_exists("openhands"):
        print("OpenHands CLI `openhands` not found; cannot run gate.", file=sys.stderr)
        return 2

    # Configure provider/model selection for the engine/proxy layers.
    os.environ["OPENHANDS_PROVIDER"] = args.provider.strip().lower()
    os.environ["OPENHANDS_MODEL"] = args.model.strip()
    os.environ["PF_OPENHANDS_MAX_TASK_CHARS"] = str(args.max_task_chars)

    # Build synthetic workspace.
    with tempfile.TemporaryDirectory() as td:
        workspace_root = Path(td) / "gate_workspace"
        workspace_root.mkdir(parents=True, exist_ok=True)
        _build_synthetic_workspace(workspace_root)

        task_text = _build_long_swebench_task_text()

        # Capability probe for expected mode.
        openhands_library_core_available = False
        try:
            from openhands.core.main import run_controller as _  # noqa: F401

            openhands_library_core_available = True
        except Exception:
            openhands_library_core_available = False

        # Normalize provider the same way as bench/swebench/provider_env.
        try:
            from bench.swebench.provider_env import normalize_openhands_provider

            provider_normalized = normalize_openhands_provider()
        except Exception:
            provider_normalized = os.environ["OPENHANDS_PROVIDER"]

        from bench.swebench.engines.openhands_engine import OpenHandsConfig, solve

        config = OpenHandsConfig(model_name=args.model, max_iterations=args.max_iterations, timeout_seconds=args.timeout)

        start = perf_counter()
        result = solve(workspace_path=workspace_root, task_text=task_text, config=config, extra_env=None)
        elapsed = perf_counter() - start

        trace = result.trace.to_dict()
        delivery = trace.get("task_delivery_report") or {}

        critical_drop = bool(delivery.get("critical_drop"))
        timeout_origin = trace.get("timeout_origin")
        first_action_latency_s = trace.get("first_action_latency_s")
        startup_budget_s = trace.get("startup_budget_s")

        timeout_before_first_action = False
        if timeout_origin == "subprocess_wall_timeout":
            if first_action_latency_s is None:
                timeout_before_first_action = True
            elif startup_budget_s is not None and first_action_latency_s > startup_budget_s:
                timeout_before_first_action = True

        execution_mode = trace.get("execution_mode") or ""
        expected_execution_mode = _compute_expected_execution_mode(
            provider_normalized=provider_normalized,
            openhands_library_core_available=openhands_library_core_available,
        )
        execution_mode_mismatch = execution_mode != expected_execution_mode

        # Prime compatibility: if normalization applied but we still saw upstream 422 responses,
        # the metric prime_422_avoided will be less than prime_payload_normalizations_applied.
        prime_422_guard = False
        if provider_normalized == "prime_intellect":
            n_applied = trace.get("prime_payload_normalizations_applied") or 0
            n_avoided = trace.get("prime_422_avoided") or 0
            prime_422_guard = n_applied > 0 and n_avoided < n_applied

        failures: dict[str, bool] = {
            "critical_drop": critical_drop,
            "timeout_before_first_action": timeout_before_first_action,
            "execution_mode_mismatch": execution_mode_mismatch,
            "prime_422_guard": prime_422_guard,
        }
        passed = not any(failures.values())

        report = {
            "passed": passed,
            "elapsed_wall_s": round(elapsed, 4),
            "provider": args.provider,
            "provider_normalized": provider_normalized,
            "model": args.model,
            "timeout": args.timeout,
            "max_iterations": args.max_iterations,
            "failures": failures,
            "trace": trace,
            "patch_diff_nonempty": bool((result.patch_diff_str or "").strip()),
        }
        print(json.dumps(report, indent=2), flush=True)

        return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

