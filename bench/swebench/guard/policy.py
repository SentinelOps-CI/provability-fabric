# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Policy for PF-Guarded Runtime: allowlists, path restrictions, max command length.

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Set, Tuple

# Local tooling only; network remains disabled (forbidden_binaries). Prefer pip install -e . for offline installs.
DEFAULT_ALLOWED = frozenset({
    "git", "python", "python3", "pytest", "bash", "sh", "cat", "ls", "find",
    "grep", "head", "tail", "sed", "awk", "diff", "mkdir", "mv", "cp", "rm",
    "touch", "chmod", "echo", "env", "which", "pwd", "cd", "true", "false",
    "pip", "make", "ruff", "nox", "tox", "coverage", "black", "mypy",
})
DEFAULT_FORBIDDEN = frozenset({
    "curl", "wget", "nc", "ncat", "ssh", "scp", "sftp", "telnet", "ftp",
    "ping", "nslookup", "dig", "netcat", "socat", "nc.traditional",
})
# /tmp omitted: many tools (pip, pytest) need a system temp dir; PF-guarded runs
# set TMPDIR under workspace/scratch/.pf_tmp. Unguarded baseline may use /tmp for caches.
DEFAULT_FORBIDDEN_PREFIXES = [
    "/etc", "/usr/lib", "/bin", "/sbin", "/root", "/home", "/var/log",
    "/dev", "/proc", "/sys", "~",
]


@dataclass
class GuardPolicy:
    """Policy configuration for the tool gateway."""

    workspace_root: Path
    max_command_length: int = 32768
    allowed_binaries: Set[str] = None
    forbidden_binaries: Set[str] = None
    forbidden_path_prefixes: List[str] = None
    network_deny: bool = True

    def __post_init__(self):
        if self.allowed_binaries is None:
            self.allowed_binaries = set(DEFAULT_ALLOWED)
        if self.forbidden_binaries is None:
            self.forbidden_binaries = set(DEFAULT_FORBIDDEN)
        if self.forbidden_path_prefixes is None:
            self.forbidden_path_prefixes = list(DEFAULT_FORBIDDEN_PREFIXES)

    def resolve_workspace(self) -> Path:
        return Path(self.workspace_root).resolve()

    def is_binary_allowed(self, binary: str) -> bool:
        base = Path(binary).name.lower()
        if base in self.forbidden_binaries:
            return False
        if base in self.allowed_binaries:
            return True
        if base.startswith("python") and "python" in self.allowed_binaries:
            return True
        if base == "pytest":
            return True
        return False

    def is_path_under_workspace(self, path: str) -> bool:
        if not path or path.strip() in ("", "-"):
            return True
        try:
            p = Path(path).expanduser().resolve()
            ws = self.resolve_workspace()
            try:
                p.relative_to(ws)
                return True
            except ValueError:
                return False
        except (OSError, RuntimeError):
            return False

    def is_path_forbidden(self, path: str) -> bool:
        if not path or path.strip() in ("", "-"):
            return False
        expanded = path.strip().expandtabs()
        for prefix in self.forbidden_path_prefixes:
            if expanded.startswith(prefix) or expanded.startswith(prefix.replace("/", "\\")):
                return True
        if ".." in Path(expanded).parts:
            try:
                if not self.is_path_under_workspace(expanded):
                    return True
            except Exception:
                return True
        return False

    def check_command_length(self, cmd: str) -> Tuple[bool, Optional[str]]:
        if len(cmd) <= self.max_command_length:
            return True, None
        return False, f"command length {len(cmd)} exceeds max {self.max_command_length}"

    def extract_first_binary(self, cmd: str) -> str:
        cmd = cmd.strip()
        if not cmd:
            return ""
        parts = re.split(r"\s+", cmd, 1)
        first = (parts[0] or "").strip()
        if first.startswith("python") or first.startswith("python3"):
            if " " in cmd:
                rest = cmd.split(None, 2)
                if len(rest) >= 2 and rest[1] == "-m":
                    return rest[2] if len(rest) > 2 else "python"
            return "python"
        return Path(first).name.lower() if first else ""
