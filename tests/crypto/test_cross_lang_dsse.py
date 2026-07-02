#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
"""Cross-language DSSE verification contract tests."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
FIXTURES = REPO_ROOT / "tests" / "fixtures" / "crypto"
ENVELOPE = FIXTURES / "dsse_sample_envelope.json"
PUBLIC_PEM = FIXTURES / "ed25519_public.pem"


def _env() -> dict[str, str]:
    env = os.environ.copy()
    env["PF_TRUST_ROOT_PEM"] = str(PUBLIC_PEM)
    env["PF_ENFORCE_DSSE"] = "1"
    return env


def _run(cmd: list[str], cwd: Path | None = None) -> dict:
    proc = subprocess.run(
        cmd,
        cwd=cwd or REPO_ROOT,
        env=_env(),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise AssertionError(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout: {proc.stdout}\nstderr: {proc.stderr}"
        )
    return json.loads(proc.stdout.strip())


def test_go_dsse_verify() -> None:
    dsse_dir = REPO_ROOT / "core" / "crypto" / "dsse"
    result = _run(
        ["go", "run", "./cmd/dsse-verify", str(ENVELOPE)],
        cwd=dsse_dir,
    )
    assert result["valid"] is True, result


def test_rust_dsse_verify() -> None:
    dsse_rs = REPO_ROOT / "core" / "crypto" / "dsse-rs"
    subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "dsse-verify", "-p", "pf-dsse"],
        cwd=REPO_ROOT,
        env=_env(),
        check=True,
    )
    bin_path = REPO_ROOT / "target" / "debug" / "dsse-verify"
    if sys.platform == "win32":
        bin_path = bin_path.with_suffix(".exe")
    result = _run([str(bin_path), str(ENVELOPE)])
    assert result["valid"] is True, result


def _find_tsc_cmd() -> list[str]:
    for rel in (
        "core/crypto/dsse-ts/node_modules/typescript/bin/tsc",
        "runtime/ledger/node_modules/typescript/bin/tsc",
    ):
        tsc_js = REPO_ROOT / rel
        if tsc_js.exists():
            return ["node", str(tsc_js)]
    return ["tsc"]


def test_typescript_dsse_verify() -> None:
    dsse_ts = REPO_ROOT / "core" / "crypto" / "dsse-ts"
    tsc_cmd = _find_tsc_cmd()
    subprocess.run(
        [*tsc_cmd, "-p", str(dsse_ts)],
        cwd=REPO_ROOT,
        check=True,
    )
    cli = dsse_ts / "dist" / "cli.js"
    result = _run(["node", str(cli), str(ENVELOPE)])
    assert result["valid"] is True, result


def test_cross_lang_outputs_match() -> None:
    dsse_dir = REPO_ROOT / "core" / "crypto" / "dsse"
    go_result = _run(["go", "run", "./cmd/dsse-verify", str(ENVELOPE)], cwd=dsse_dir)

    subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "dsse-verify", "-p", "pf-dsse"],
        cwd=REPO_ROOT,
        env=_env(),
        check=True,
    )
    bin_path = REPO_ROOT / "target" / "debug" / "dsse-verify"
    if sys.platform == "win32":
        bin_path = bin_path.with_suffix(".exe")
    rust_result = _run([str(bin_path), str(ENVELOPE)])

    assert go_result == rust_result, (go_result, rust_result)


if __name__ == "__main__":
    test_go_dsse_verify()
    test_rust_dsse_verify()
    test_typescript_dsse_verify()
    test_cross_lang_outputs_match()
    print("cross-lang DSSE tests passed")
