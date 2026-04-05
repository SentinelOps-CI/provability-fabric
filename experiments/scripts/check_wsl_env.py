#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Preflight checks for the real run + harness loop (Step 2). Full checks require Linux/WSL:
# - resource (SWE-bench harness), fcntl (POSIX file locking used by tooling), Docker, datasets, swebench;
#   openhands optional when using --skip-openhands (direct_agent engine).
# On native Windows (PowerShell + Windows Python), Linux-only modules are skipped; the script
# still checks requests and Docker, prints where to run the full preflight, and exits 0 unless
# requests fails. Use --strict-linux from Linux CI to keep hard failures on missing deps.
# Run from repository root: python experiments/scripts/check_wsl_env.py

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys


def _is_docker_failure(message: str) -> bool:
    return message.startswith("docker")


def _early_exit_if_failed(failed: list[str]) -> int | None:
    # PF_WSL_PREFLIGHT_MINIMAL=1: unit tests only; avoid importing datasets after an early failure.
    if failed and os.environ.get("PF_WSL_PREFLIGHT_MINIMAL") == "1":
        print("Preflight failed. Do not proceed to runs.", file=sys.stderr)
        for f in failed:
            print("  - %s" % f, file=sys.stderr)
        print("", file=sys.stderr)
        print("Install deps in WSL using a dedicated venv (avoids conflicts with other projects):", file=sys.stderr)
        print("  bash experiments/scripts/setup_swebench_venv.sh", file=sys.stderr)
        print("Or manually: python3 -m venv .venv-wsl && . .venv-wsl/bin/activate", file=sys.stderr)
        print("  pip install -r bench/swebench/requirements-swebench.txt", file=sys.stderr)
        print("Then re-run this script (or run-baseline-pf-cycle.sh; it will use .venv-wsl if present).", file=sys.stderr)
        return 1
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description="WSL/Linux preflight for SWE-bench + agent engine (OpenHands or direct_agent).")
    ap.add_argument(
        "--docker-pull",
        action="store_true",
        help="After docker info, run docker pull hello-world (slower; confirms registry reachability).",
    )
    ap.add_argument(
        "--strict-linux",
        action="store_true",
        help="Fail if resource/fcntl/datasets/openhands missing (use on Linux/WSL; default on Windows is relaxed).",
    )
    ap.add_argument(
        "--skip-openhands",
        action="store_true",
        help="With --strict-linux: do not require the openhands package (for SWE-bench runs with --engine direct_agent).",
    )
    args = ap.parse_args()
    failed: list[str] = []
    is_win = sys.platform == "win32"
    relaxed_win = is_win and not args.strict_linux
    strict = not relaxed_win

    if relaxed_win:
        print(
            "check_wsl_env: native Windows — full bench preflight is for WSL/Linux only "
            "(resource/fcntl/datasets/openhands skipped here).",
            file=sys.stderr,
        )

    if strict:
        try:
            import resource  # noqa: F401
            print("resource ok")
        except ImportError as e:
            failed.append("resource: %s" % e)

        try:
            import fcntl  # noqa: F401
            print("fcntl ok")
        except ImportError as e:
            failed.append("fcntl: %s" % e)
    else:
        print("resource+fcntl: skipped (Windows)")

    code = _early_exit_if_failed(failed)
    if code is not None:
        return code

    try:
        r = subprocess.run(
            ["docker", "info"],
            capture_output=True,
            text=True,
            timeout=60,
        )
        if r.returncode == 0:
            print("docker ok")
        elif r.returncode is not None and r.returncode < 0:
            sig = -r.returncode
            msg = (
                "docker: docker info crashed (signal %s). On WSL with Docker Desktop issues, "
                "run a native dockerd and set DOCKER_HOST; see experiments/exp-step2-lite-smoke/commands.md "
                "\"Docker WSL stable setup\"." % sig
            )
            if strict:
                failed.append(msg)
            else:
                print("Warning: %s" % msg, file=sys.stderr)
        else:
            msg = "docker: docker info exited %s" % r.returncode
            if strict:
                failed.append(msg)
            else:
                print("Warning: %s (bench uses Docker from WSL.)" % msg, file=sys.stderr)
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError) as e:
        if isinstance(e, FileNotFoundError):
            msg = (
                "docker: command not found (install Docker Engine; SWE-bench harness needs it). "
                "Debian/Ubuntu: sudo apt-get update && sudo apt-get install -y docker.io && "
                "sudo systemctl enable --now docker; then sudo usermod -aG docker \"$USER\" "
                "and re-login (or newgrp docker), or use sudo docker. Verify: docker run --rm hello-world"
            )
        else:
            msg = "docker: %s" % e
        if strict:
            failed.append(msg)
        else:
            print("Warning: %s (bench uses Docker inside WSL.)" % msg, file=sys.stderr)

    if not failed and args.docker_pull:
        try:
            pr = subprocess.run(
                ["docker", "pull", "hello-world"],
                capture_output=True,
                text=True,
                timeout=180,
            )
            if pr.returncode == 0:
                print("docker pull hello-world ok")
            else:
                failed.append("docker pull: exited %s" % pr.returncode)
        except (FileNotFoundError, subprocess.TimeoutExpired, OSError) as e:
            failed.append("docker pull: %s" % e)

    code = _early_exit_if_failed(failed)
    if code is not None:
        return code

    try:
        import requests  # noqa: F401  # used by datasets; catch IndentationError/corruption before long runs
        print("requests ok")
    except (ImportError, SyntaxError, IndentationError) as e:
        failed.append("requests: %s (fix: pip install --force-reinstall requests)" % e)

    code = _early_exit_if_failed(failed)
    if code is not None:
        return code

    if strict:
        try:
            import datasets  # noqa: F401
            import swebench  # noqa: F401
            print("datasets+swebench ok")
        except ImportError as e:
            failed.append("datasets+swebench: %s" % e)

        if args.skip_openhands:
            print("openhands: skipped (--skip-openhands)")
        else:
            try:
                import openhands  # noqa: F401
                print("openhands ok")
            except ImportError as e:
                failed.append("openhands: %s" % e)
    else:
        print("datasets+swebench+openhands: skipped (install in WSL venv for bench runs)")

    if failed:
        print("Preflight failed. Do not proceed to runs.", file=sys.stderr)
        for f in failed:
            print("  - %s" % f, file=sys.stderr)
        print("", file=sys.stderr)
        non_docker = [f for f in failed if not _is_docker_failure(f)]
        if not non_docker:
            print(
                "Only Docker is missing or unreachable; Python imports above are fine.",
                file=sys.stderr,
            )
            print("", file=sys.stderr)
            print("Quick setup on Debian bookworm / Ubuntu:", file=sys.stderr)
            print("  sudo apt-get update && sudo apt-get install -y docker.io", file=sys.stderr)
            print("  sudo systemctl enable --now docker", file=sys.stderr)
            print('  sudo usermod -aG docker "$USER" && newgrp docker   # or log out and back in', file=sys.stderr)
            print("  docker run --rm hello-world", file=sys.stderr)
        else:
            print("Install deps in WSL using a dedicated venv (avoids conflicts with other projects):", file=sys.stderr)
            print("  bash experiments/scripts/setup_swebench_venv.sh", file=sys.stderr)
            print("Or manually: python3 -m venv .venv-wsl && . .venv-wsl/bin/activate", file=sys.stderr)
            print("  pip install -r bench/swebench/requirements-swebench.txt", file=sys.stderr)
            print("Then re-run this script (or run-baseline-pf-cycle.sh; it will use .venv-wsl if present).", file=sys.stderr)
        return 1

    if relaxed_win:
        print(
            "Windows preflight: OK for repo scripts. Before baseline/PF runs: open WSL, "
            "activate .venv-wsl, run `python experiments/scripts/check_wsl_env.py` again.",
            file=sys.stderr,
        )
    elif strict and not shutil.which("tmux") and not shutil.which("screen"):
        print(
            "Note: neither tmux nor screen on PATH. Long jobs over SSH stop if the session drops; "
            "install one: bash experiments/scripts/install_vm_runner_extras.sh",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
