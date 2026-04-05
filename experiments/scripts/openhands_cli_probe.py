#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Provider-neutral OpenHands CLI probe harness.
#
# Purpose:
# - Compare provider/runtime behavior via a single direct OpenHands CLI execution.
# - Emit machine-readable summary including latency metrics derived from --json events.
#
# Notes:
# - This script is "best-effort": if OpenHands output shape doesn't contain timestamps,
#   latency metrics may be null rather than failing.

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from time import perf_counter


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


@dataclass
class ProbeSummary:
    provider: str
    provider_normalized: str
    model_raw: str
    model_effective: str | None
    elapsed_wall_s: float
    events_count: int
    first_action_latency_s: float | None
    first_file_edit_latency_s: float | None
    patch_diff_nonempty: bool
    openhands_exit_code: int
    error: str | None = None


def _require_openhands() -> None:
    if not shutil_which("openhands"):
        print("OpenHands CLI binary `openhands` not found in PATH.", file=sys.stderr)
        sys.exit(2)


def shutil_which(cmd: str) -> str | None:
    from shutil import which

    return which(cmd)


def _build_tiny_git_repo(repo_dir: Path) -> None:
    repo_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init"], cwd=str(repo_dir), check=True, capture_output=True, text=True)
    (repo_dir / "hello.py").write_text("def hello():\n    return 'hello'\n", encoding="utf-8")
    subprocess.run(
        ["git", "add", "."],
        cwd=str(repo_dir),
        check=True,
        capture_output=True,
        text=True,
    )
    subprocess.run(
        ["git", "-c", "user.name=pf", "-c", "user.email=pf@example.com", "commit", "-m", "init"],
        cwd=str(repo_dir),
        check=True,
        capture_output=True,
        text=True,
    )


def _build_task_prompt() -> str:
    # Keep prompt short to avoid CLI command length and tmux command-too-long failures.
    return (
        "# Task: GitHub issue — implement the fix in code\n"
        "**Leave your edits in place when done.**\n\n"
        "Edit `hello.py` so that `hello()` returns the string 'ok'.\n\n"
        "**Reminder:** Implement the fix by editing files (use edit_file / file_editor).\n"
        "**Efficiency:** Keep changes minimal.\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Direct OpenHands CLI probe (provider-neutral).")
    parser.add_argument("--provider", type=str, required=False, default=os.environ.get("OPENHANDS_PROVIDER", "openai"))
    parser.add_argument("--model", type=str, required=False, default=os.environ.get("OPENHANDS_MODEL", "gpt-4o-mini"))
    parser.add_argument("--timeout", type=int, default=int(os.environ.get("OPENHANDS_PROBE_TIMEOUT_S", "180")))
    parser.add_argument("--task-file-max-bytes", type=int, default=32_000)
    args = parser.parse_args()

    provider_raw = args.provider.strip().lower()
    model_raw = args.model.strip()

    _require_openhands()

    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        repo_dir = root / "repo"
        _build_tiny_git_repo(repo_dir)

        # OpenHands requires a work dir and persistence config.
        work_dir = repo_dir
        persistence_dir = root / "openhands_persistence"
        persistence_dir.mkdir(parents=True, exist_ok=True)
        os.environ["OH_PERSISTENCE_DIR"] = str(persistence_dir.resolve())
        os.environ["OPENHANDS_PERSISTENCE_DIR"] = str(persistence_dir.resolve())
        os.environ["OPENHANDS_WORK_DIR"] = str(work_dir.resolve())

        # Provider/base/model wiring (provider-neutral; relies on existing API keys in env).
        try:
            from bench.swebench.provider_env import effective_llm_model, llm_credentials, normalize_openhands_provider
        except ImportError:
            from bench.swebench import provider_env as _pe  # type: ignore[import-not-found]

            effective_llm_model = _pe.effective_llm_model
            llm_credentials = _pe.llm_credentials
            normalize_openhands_provider = _pe.normalize_openhands_provider

        os.environ["OPENHANDS_PROVIDER"] = provider_raw
        api_key, base_url, prov_normalized = llm_credentials()
        effective_model = effective_llm_model(prov_normalized, model_raw)

        if not api_key:
            print("Missing API key for the selected OPENHANDS_PROVIDER.", file=sys.stderr)
            return 3

        os.environ["LLM_API_KEY"] = api_key
        os.environ["LLM_BASE_URL"] = base_url or ""
        os.environ["LLM_MODEL"] = effective_model
        os.environ["OPENHANDS_MODEL"] = model_raw

        task_text = _build_task_prompt()
        if len(task_text.encode("utf-8")) > args.task_file_max_bytes:
            raise ValueError("Probe prompt unexpectedly large; reduce task.")

        task_file = root / "openhands_task.txt"
        task_file.write_text(task_text, encoding="utf-8")

        cmd = [
            "openhands",
            "--headless",
            "--override-with-envs",
            "--json",
            "--file",
            str(task_file.resolve()),
        ]

        start = perf_counter()
        proc = subprocess.run(
            cmd,
            cwd=str(repo_dir.resolve()),
            env=dict(os.environ),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=args.timeout,
        )
        elapsed = perf_counter() - start
        stdout = proc.stdout or ""

        # Parse events from CLI output using OpenHands engine helpers.
        events_count = 0
        first_action_latency_s = None
        first_file_edit_latency_s = None
        patch_diff_nonempty = False
        error = None

        try:
            from bench.swebench.engines.openhands_engine import (
                _extract_latency_metrics_from_events,
                _fill_trace_from_events,
                _parse_openhands_cli_stdout_events,
                EngineTrace,
                _is_file_edit_tool,
            )

            raw_events = _parse_openhands_cli_stdout_events(stdout)
            events_count = len(raw_events)
            first_action_latency_s, first_file_edit_latency_s = _extract_latency_metrics_from_events(raw_events)

            trace = EngineTrace(raw_events=raw_events)
            _fill_trace_from_events(trace)
            patch_diff_nonempty = bool(trace.files_modified)
        except Exception as e:
            error = f"probe_event_parse_failed: {e}"

        # Also verify that git diff is non-empty.
        try:
            diff = subprocess.run(
                ["git", "diff", "HEAD"],
                cwd=str(repo_dir.resolve()),
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30,
            )
            patch_diff_nonempty = patch_diff_nonempty or bool((diff.stdout or "").strip())
        except Exception:
            pass

        summary = ProbeSummary(
            provider=provider_raw,
            provider_normalized=prov_normalized,
            model_raw=model_raw,
            model_effective=effective_model,
            elapsed_wall_s=round(elapsed, 4),
            events_count=events_count,
            first_action_latency_s=first_action_latency_s,
            first_file_edit_latency_s=first_file_edit_latency_s,
            patch_diff_nonempty=patch_diff_nonempty,
            openhands_exit_code=int(proc.returncode),
            error=error,
        )

        print(json.dumps(asdict(summary), indent=2), flush=True)
        if proc.returncode != 0:
            return 4
        return 0


if __name__ == "__main__":
    raise SystemExit(main())

