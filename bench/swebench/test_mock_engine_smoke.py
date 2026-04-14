#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Smoke tests for mock engine (no OpenHands). Ensures:
# - Baseline mode: no violation events.
# - Guarded mode: exactly one violation event with reason_code=binary_forbidden.

from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path

# Run from bench/swebench or repo root
_BENCH = Path(__file__).resolve().parent
if str(_BENCH) not in sys.path:
    sys.path.insert(0, str(_BENCH))
_REPO_ROOT = _BENCH.parent.parent

GUARD_SHELL = _BENCH / "guard" / ("pf_guard_exec.bat" if os.name == "nt" else "pf_guard_exec.sh")


def test_baseline_no_violations() -> None:
    """In baseline mode (no guard env) no violation events are written."""
    from engines.mock_engine import solve

    result = solve(workspace_path=None, task_text="", config=None, extra_env=None)
    assert result.success
    trace = result.trace.to_dict()
    tool_calls = trace.get("tool_calls") or []
    assert len(tool_calls) >= 1
    assert result.patch_diff_str
    # No guard was used, so no events file to check; we just ensure no crash and trace shape
    assert "prompts_sent" in trace
    assert "tool_calls" in trace


def test_guarded_exactly_one_violation() -> None:
    """In guarded mode exactly one violation event with reason_code=binary_forbidden."""
    if not GUARD_SHELL.exists():
        raise RuntimeError(f"Guard shell not found: {GUARD_SHELL} (run from repo root)")

    from engines.mock_engine import solve, EXPECTED_VIOLATION_REASON_CODE

    with tempfile.TemporaryDirectory(prefix="pf_mock_smoke_") as tmp:
        workspace = Path(tmp) / "ws"
        workspace.mkdir()
        (workspace / "repo").mkdir()
        evidence = Path(tmp) / "evidence"
        evidence.mkdir()

        extra_env = {
            "SHELL": str(GUARD_SHELL.resolve()),
            "PF_GUARD_WORKSPACE": str(workspace.resolve()),
            "PF_GUARD_LEDGER_DIR": str(evidence.resolve()),
            "PF_GUARD_RUN_ID": "smoke",
            "PF_REPO_ROOT": str(_REPO_ROOT.resolve()),
        }

        result = solve(
            workspace_path=workspace,
            task_text="",
            config=None,
            extra_env=extra_env,
        )
        assert result.success

        events_file = evidence / "events.jsonl"
        assert events_file.exists(), "Guard should write events.jsonl in guarded mode"
        events = []
        with open(events_file, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                events.append(json.loads(line))

        violations = [e for e in events if e.get("event_type") == "violation"]
        assert len(violations) == 1, f"Expected exactly one violation event, got {len(violations)}: {events}"
        payload = violations[0].get("payload") or {}
        reason = payload.get("reason_code") or payload.get("violation", "")
        assert reason == EXPECTED_VIOLATION_REASON_CODE, (
            f"Expected reason_code={EXPECTED_VIOLATION_REASON_CODE}, got reason_code={payload.get('reason_code')} violation={payload.get('violation')}"
        )


def main() -> int:
    try:
        test_baseline_no_violations()
        print("PASS: baseline (no violations)")
        test_guarded_exactly_one_violation()
        print("PASS: guarded (exactly one violation, reason_code=binary_forbidden)")
        return 0
    except Exception as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
