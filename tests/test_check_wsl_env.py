# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Contract tests for check_wsl_env.py: fail with clear reason when resource/fcntl missing,
# Docker unavailable, or Python deps (datasets, swebench, openhands) missing.

from __future__ import annotations

import io
import sys
import types
from pathlib import Path
from unittest import mock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def _run_main(
    fail_resource: bool = False,
    fail_fcntl: bool = False,
    docker_returncode: int = 0,
    docker_raises: Exception | None = None,
    fail_datasets_swebench: bool = False,
    fail_openhands: bool = False,
    argv: list[str] | None = None,
    minimal: bool = True,
) -> tuple[int, str, str]:
    """Run check_wsl_env.main() with optional mocks. Returns (code, stdout, stderr)."""
    import importlib

    import builtins

    mod = importlib.import_module("experiments.scripts.check_wsl_env")
    real_import = builtins.__import__
    fail_imports = set()
    if fail_resource:
        fail_imports.add("resource")
    if fail_fcntl:
        fail_imports.add("fcntl")
    if fail_datasets_swebench:
        fail_imports.add("datasets")
        fail_imports.add("swebench")
    if fail_openhands:
        fail_imports.add("openhands")

    def mock_import(name, *args, **kwargs):
        if name in fail_imports:
            raise ImportError("No module named '%s'" % name)
        return real_import(name, *args, **kwargs)

    stdout = io.StringIO()
    stderr = io.StringIO()
    av = argv if argv is not None else ["check_wsl_env.py", "--strict-linux"]
    env_patch = {"PF_WSL_PREFLIGHT_MINIMAL": "1"} if minimal else {}
    stubbed: list[str] = []
    popped: dict[str, object | None] = {}
    for mod_name in fail_imports:
        if mod_name in sys.modules:
            popped[mod_name] = sys.modules.pop(mod_name)
    code = 1
    try:
        if sys.platform == "win32" and not fail_resource and "resource" not in sys.modules:
            sys.modules["resource"] = types.ModuleType("resource")
            stubbed.append("resource")
        if sys.platform == "win32" and not fail_fcntl and not fail_resource and "fcntl" not in sys.modules:
            sys.modules["fcntl"] = types.ModuleType("fcntl")
            stubbed.append("fcntl")

        with mock.patch.dict(mod.os.environ, env_patch, clear=False):
            with mock.patch.object(mod.sys, "argv", av):
                with mock.patch("builtins.__import__", side_effect=mock_import):
                    with mock.patch.object(mod.subprocess, "run") as m_run:
                        if docker_raises:
                            m_run.side_effect = docker_raises
                        else:
                            m_run.return_value = mock.Mock(returncode=docker_returncode, stdout="", stderr="")
                        with mock.patch("sys.stdout", stdout), mock.patch("sys.stderr", stderr):
                            code = mod.main()
    finally:
        for name in stubbed:
            sys.modules.pop(name, None)
        for name, prev in popped.items():
            if prev is not None:
                sys.modules[name] = prev
    return code, stdout.getvalue(), stderr.getvalue()


def test_check_wsl_env_fails_when_resource_missing():
    """On some non-Linux environments, resource module is missing; script should fail with clear message."""
    code, stdout, stderr = _run_main(fail_resource=True)
    assert code != 0
    assert "resource" in stderr or "Preflight failed" in stderr


def test_check_wsl_env_fails_when_fcntl_missing():
    """On non-WSL (e.g. Windows), fcntl is missing; script should fail with clear message."""
    code, stdout, stderr = _run_main(fail_fcntl=True)
    assert code != 0
    assert "fcntl" in stderr or "Preflight failed" in stderr


def test_check_wsl_env_fails_when_docker_unavailable():
    """When Docker is not running or not installed, script should fail with docker-related reason."""
    code, stdout, stderr = _run_main(docker_returncode=1)
    assert code != 0
    assert "docker" in stderr.lower() or "Preflight failed" in stderr


def test_check_wsl_env_fails_when_docker_not_found():
    """When docker command is not found, script should fail with docker in message."""
    code, stdout, stderr = _run_main(docker_raises=FileNotFoundError("docker not found"))
    assert code != 0
    assert "docker" in stderr.lower() or "Preflight failed" in stderr


def test_check_wsl_env_fails_when_datasets_or_swebench_missing():
    """When datasets or swebench not installed, script should fail with specific reason."""
    code, stdout, stderr = _run_main(fail_datasets_swebench=True)
    assert code != 0
    assert "datasets" in stderr or "swebench" in stderr or "Preflight failed" in stderr


def test_check_wsl_env_fails_when_openhands_missing():
    """When openhands not installed, script should fail with specific reason."""
    code, stdout, stderr = _run_main(fail_openhands=True)
    assert code != 0
    assert "openhands" in stderr or "Preflight failed" in stderr


def test_check_wsl_env_strict_skip_openhands_does_not_import_openhands():
    """--skip-openhands allows strict preflight when openhands is not installed."""
    code, stdout, stderr = _run_main(
        fail_openhands=True,
        argv=["check_wsl_env.py", "--strict-linux", "--skip-openhands"],
    )
    assert code == 0
    assert "skipped (--skip-openhands)" in stdout


def test_check_wsl_env_passes_when_all_mocked_ok():
    """When all checks pass (mocked: fake modules + docker ok), script exits 0 and prints ok lines."""
    import importlib

    mod = importlib.import_module("experiments.scripts.check_wsl_env")
    fake = mock.MagicMock()
    to_restore = {}
    for name in ("resource", "fcntl", "datasets", "swebench", "openhands"):
        to_restore[name] = sys.modules.get(name)
        sys.modules[name] = fake
    try:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with mock.patch.object(mod.sys, "argv", ["check_wsl_env.py", "--strict-linux"]):
            with mock.patch.object(mod.subprocess, "run") as m_run:
                m_run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
                with mock.patch("sys.stdout", stdout), mock.patch("sys.stderr", stderr):
                    code = mod.main()
        assert code == 0
        assert "ok" in stdout.getvalue().lower()
    finally:
        for name, m in to_restore.items():
            if m is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = m


@pytest.mark.skipif(sys.platform != "win32", reason="relaxed path is Windows-only")
def test_check_wsl_env_windows_relaxed_skips_linux_modules():
    """Native Windows: missing resource/datasets/openhands does not fail; requests ok."""
    code, stdout, stderr = _run_main(argv=["check_wsl_env.py"], minimal=False)
    assert code == 0
    assert "skipped" in stdout.lower() or "windows" in stderr.lower()
    assert "requests ok" in stdout
