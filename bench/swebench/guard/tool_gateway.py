# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Tool gateway: mediates shell exec (and path checks for file ops). Enforces
# network=off (via binary deny), workspace-only writes, max command length,
# allowlist of binaries. Fails closed on violation and records to ledger.

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from .ledger_stream import LedgerStream
from .policy import GuardPolicy
from .redact import redact_secrets

# Structured suggestions for agent adaptation (do not open network; revise plan and proceed)
DENIAL_SUGGESTIONS = {
    "empty_command": "Provide a non-empty command.",
    "command_too_long": "Shorten the command or split into multiple steps.",
    "binary_forbidden": "Network is unavailable; do not attempt external fetch. Use local docs, pip install -e ., or offline tools.",
    "path_forbidden": "Write only inside the workspace. Do not write to /etc, /tmp, /home, or paths outside the repo.",
    "path_outside_workspace": "Keep all file operations under the workspace (repo) directory.",
    "timeout": "Command timed out; try a smaller scope or fewer iterations.",
    "execution_error": "Command failed; check syntax and environment.",
}


@dataclass
class CommandResult:
    allowed: bool
    exit_code: Optional[int] = None
    stdout: str = ""
    stderr: str = ""
    violation: Optional[str] = None
    reason_code: str = ""
    suggestion: Optional[str] = None


def _extract_paths_from_command(cmd: str) -> List[str]:
    """Heuristic: extract path-like tokens that might be write targets."""
    paths = []
    for m in re.finditer(r"(?:^|\s)(?:>|>>)\s*([^\s&|;]+)", cmd):
        paths.append(m.group(1).strip())
    for m in re.finditer(r"\s-o\s+([^\s]+)", cmd):
        paths.append(m.group(1).strip())
    for m in re.finditer(r"\s-f\s+([^\s]+)", cmd):
        paths.append(m.group(1).strip())
    for m in re.finditer(r'["\']([^"\']+)["\']', cmd):
        p = m.group(1).strip()
        if "/" in p or "\\" in p or p.endswith((".py", ".txt", ".json")):
            paths.append(p)
    return paths


class ToolGateway:
    """Mediates tool execution: shell exec, enforces policy, writes to ledger."""

    def __init__(self, policy: GuardPolicy, ledger: LedgerStream):
        self.policy = policy
        self.ledger = ledger

    def check_command(self, cmd: str, cwd: Path) -> Tuple[bool, Optional[str], str]:
        """Return (allowed, violation_message, reason_code). reason_code for denials: empty_command, command_too_long, binary_forbidden, path_forbidden, path_outside_workspace."""
        if not cmd or not cmd.strip():
            return False, "empty command", "empty_command"
        ok, err = self.policy.check_command_length(cmd)
        if not ok:
            return False, err or "command too long", "command_too_long"
        binary = self.policy.extract_first_binary(cmd)
        if not binary:
            return False, "could not determine binary", "binary_forbidden"
        # Deny git/pip when command clearly fetches from network (URLs)
        if binary in ("git", "pip") and (
            "https://" in cmd or "http://" in cmd or "git+https" in cmd or "git+http" in cmd
        ):
            return False, "network/URL not allowed for %s (use offline install or local repo)" % binary, "binary_forbidden"
        if not self.policy.is_binary_allowed(binary):
            return False, f"binary not allowed: {binary} (network/forbidden)", "binary_forbidden"
        for path in _extract_paths_from_command(cmd):
            if self.policy.is_path_forbidden(path):
                return False, f"path not allowed (outside workspace): {path}", "path_forbidden"
            try:
                resolved = (cwd / path).resolve()
                if not self.policy.is_path_under_workspace(str(resolved)):
                    return False, f"path outside workspace: {path}", "path_outside_workspace"
            except Exception:
                pass
        return True, None, ""

    def execute_command(
        self,
        cmd: str,
        cwd: Path,
        timeout_seconds: int = 300,
    ) -> CommandResult:
        """Execute command through the gateway. Fail closed on violation. Denials are recoverable (single command fails, agent can continue) unless PF_GUARD_FAIL_FAST is set."""
        cwd = Path(cwd).resolve()
        allowed, violation, reason_code = self.check_command(cmd, cwd)
        if not allowed:
            self.ledger.append_tool_call(
                tool="shell",
                allowed=False,
                command_or_path=cmd[:2000],
                violation=violation,
                reason_code=reason_code,
            )
            suggestion = DENIAL_SUGGESTIONS.get(reason_code, "If a command is denied, revise plan and proceed.")
            return CommandResult(allowed=False, violation=violation, reason_code=reason_code, suggestion=suggestion)

        try:
            proc = subprocess.run(
                ["bash", "-c", cmd],
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
            )
            stdout_r = redact_secrets(proc.stdout or "")
            stderr_r = redact_secrets(proc.stderr or "")
            self.ledger.append_tool_call(
                tool="shell",
                allowed=True,
                command_or_path=cmd[:2000],
                exit_code=proc.returncode,
                stdout_redacted=stdout_r[:8000] if stdout_r else None,
                stderr_redacted=stderr_r[:8000] if stderr_r else None,
            )
            return CommandResult(
                allowed=True,
                exit_code=proc.returncode,
                stdout=proc.stdout or "",
                stderr=proc.stderr or "",
            )
        except subprocess.TimeoutExpired:
            self.ledger.append_tool_call(
                tool="shell",
                allowed=True,
                command_or_path=cmd[:2000],
                violation="timeout",
                reason_code="timeout",
            )
            return CommandResult(allowed=True, exit_code=-1, violation="timeout")
        except Exception as e:
            self.ledger.append_tool_call(
                tool="shell",
                allowed=True,
                command_or_path=cmd[:2000],
                violation=str(e)[:500],
                reason_code="execution_error",
            )
            return CommandResult(allowed=True, exit_code=-1, violation=str(e))
