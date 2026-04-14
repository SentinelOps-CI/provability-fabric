# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Policy regression tests (deny/allow matrix): lock guard behavior with explicit tests.

from __future__ import annotations

import sys
from pathlib import Path
from unittest import mock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.guard.policy import GuardPolicy
from bench.swebench.guard.tool_gateway import ToolGateway


def _gateway(workspace: Path):
    policy = GuardPolicy(workspace_root=workspace)
    ledger = mock.Mock()
    ledger.append_tool_call = mock.Mock(return_value=None)
    return ToolGateway(policy=policy, ledger=ledger)


def test_policy_denies_curl():
    """Deny curl (network binary)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, reason = gw.check_command("curl -s https://example.com", ws)
    assert allowed is False
    assert reason == "binary_forbidden"


def test_policy_denies_wget():
    """Deny wget (network binary)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, reason = gw.check_command("wget https://example.com", ws)
    assert allowed is False
    assert reason == "binary_forbidden"


def test_policy_denies_git_clone_https():
    """Deny git clone https://... (network fetch)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, reason = gw.check_command("git clone https://github.com/org/repo.git", ws)
    assert allowed is False
    assert reason == "binary_forbidden"


def test_policy_denies_pip_install_git_https():
    """Deny pip install git+https://... (network fetch)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, reason = gw.check_command("pip install git+https://github.com/org/pkg.git", ws)
    assert allowed is False
    assert reason == "binary_forbidden"


def test_policy_allows_python_m_pytest():
    """Allow python -m pytest (module name only so extract_first_binary returns pytest)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, _ = gw.check_command("python -m pytest", ws)
    assert allowed is True


def test_policy_allows_pip_install_editable_offline():
    """Allow pip install -e . (offline editable install)."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, _ = gw.check_command("pip install -e .", ws)
    assert allowed is True


def test_policy_allows_make_test():
    """Allow make test."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed, _, _ = gw.check_command("make test", ws)
    assert allowed is True


def test_policy_allows_grep_and_sed():
    """Allow grep and sed."""
    ws = Path("/fake/workspace/repo")
    gw = _gateway(ws)
    allowed1, _, _ = gw.check_command("grep -r pattern src/", ws)
    allowed2, _, _ = gw.check_command("sed -i 's/a/b/' file.txt", ws)
    assert allowed1 is True
    assert allowed2 is True


def test_policy_allows_write_under_workspace():
    """Allow writes only under workspace (path under cwd)."""
    ws = Path("/fake/workspace/repo").resolve()
    gw = _gateway(ws)
    allowed, _, _ = gw.check_command("echo foo > src/output.txt", ws)
    assert allowed is True


def test_policy_denies_write_outside_workspace():
    """Deny write to path outside workspace (e.g. /tmp)."""
    ws = Path("/fake/workspace/repo").resolve()
    gw = _gateway(ws)
    # /tmp is in forbidden_path_prefixes
    allowed, _, reason = gw.check_command("echo foo > /tmp/out.txt", ws)
    assert allowed is False
    assert reason in ("path_forbidden", "path_outside_workspace")


def test_policy_denies_output_redirection_to_forbidden_path():
    """Deny -o or > to forbidden path (/etc, /tmp, etc.)."""
    ws = Path("/fake/workspace/repo").resolve()
    gw = _gateway(ws)
    # -o is extracted by _extract_paths_from_command; /etc is forbidden
    allowed, _, reason = gw.check_command("python script.py -o /etc/out.json", ws)
    assert allowed is False
    assert reason in ("path_forbidden", "path_outside_workspace")
