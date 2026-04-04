# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# CLI executor for PF-Guarded Runtime. Invoked as SHELL by OpenHands;
# receives -c "command", runs through the tool gateway, exits with command exit code.

from __future__ import annotations

import os
import sys
from pathlib import Path

# Allow running as script or module; ensure guard package is importable
def _setup_path():
    guard_dir = Path(__file__).resolve().parent
    if guard_dir.name == "guard":
        repo_root = guard_dir.parent.parent.parent
        if str(repo_root) not in sys.path:
            sys.path.insert(0, str(repo_root))


if __name__ == "__main__":
    _setup_path()

from bench.swebench.guard.ledger_stream import LedgerStream
from bench.swebench.guard.policy import GuardPolicy
from bench.swebench.guard.tool_gateway import ToolGateway


def main() -> int:
    workspace = os.environ.get("PF_GUARD_WORKSPACE", "")
    ledger_dir = os.environ.get("PF_GUARD_LEDGER_DIR", "")
    events_path = os.environ.get("PF_GUARD_EVENTS_PATH", "")
    run_id = os.environ.get("PF_GUARD_RUN_ID", "run")

    if not workspace or not (ledger_dir or events_path):
        sys.stderr.write("PF Guard executor: set PF_GUARD_WORKSPACE and PF_GUARD_LEDGER_DIR or PF_GUARD_EVENTS_PATH\n")
        return 127

    ws_root = Path(workspace).resolve()
    if events_path:
        out_path = Path(events_path)
    else:
        out_path = Path(ledger_dir) / "events.jsonl"
    out_path.parent.mkdir(parents=True, exist_ok=True)

    policy = GuardPolicy(workspace_root=ws_root)
    ledger = LedgerStream(output_path=out_path, run_id=run_id)
    gateway = ToolGateway(policy=policy, ledger=ledger)

    cmd = None
    if len(sys.argv) >= 3 and sys.argv[1] == "-c":
        cmd = sys.argv[2]
    if not cmd and not sys.argv[1:]:
        line = sys.stdin.readline()
        if line:
            cmd = line.strip()
    if not cmd:
        sys.stderr.write("PF Guard executor: no command (-c 'cmd' or stdin)\n")
        return 126

    cwd = ws_root / "repo" if (ws_root / "repo").is_dir() else ws_root
    result = gateway.execute_command(cmd, cwd=cwd)
    if not result.allowed:
        reason = getattr(result, "reason_code", None) or "binary_forbidden"
        suggestion = getattr(result, "suggestion", None) or "If a command is denied, revise plan and proceed."
        sys.stderr.write(f"DENIED: reason={reason}; suggestion={suggestion}; message={result.violation or ''}\n")
        return 125
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    return result.exit_code if result.exit_code is not None else 0


if __name__ == "__main__":
    sys.exit(main())
