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


def _env(*, enforce: str | None = "1", trust_root: bool = True) -> dict[str, str]:
    env = os.environ.copy()
    if trust_root:
        env["PF_TRUST_ROOT_PEM"] = str(PUBLIC_PEM)
    else:
        env.pop("PF_TRUST_ROOT_PEM", None)
    if enforce is None:
        env.pop("PF_ENFORCE_DSSE", None)
    else:
        env["PF_ENFORCE_DSSE"] = enforce
    return env


def _run(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> dict:
    proc = subprocess.run(
        cmd,
        cwd=cwd or REPO_ROOT,
        env=env or _env(),
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
        "core/sdk/typescript/node_modules/typescript/bin/tsc",
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


def test_unset_enforce_matches_explicit_one() -> None:
    """Unset PF_ENFORCE_DSSE must enforce the same as PF_ENFORCE_DSSE=1."""
    dsse_dir = REPO_ROOT / "core" / "crypto" / "dsse"
    with_one = _run(
        ["go", "run", "./cmd/dsse-verify", str(ENVELOPE)],
        cwd=dsse_dir,
        env=_env(enforce="1"),
    )
    with_unset = _run(
        ["go", "run", "./cmd/dsse-verify", str(ENVELOPE)],
        cwd=dsse_dir,
        env=_env(enforce=None),
    )
    assert with_one == with_unset
    assert with_unset["valid"] is True


def test_go_rejects_without_trust_root_when_unset() -> None:
    dsse_dir = REPO_ROOT / "core" / "crypto" / "dsse"
    proc = subprocess.run(
        ["go", "run", "./cmd/dsse-verify", str(ENVELOPE)],
        cwd=dsse_dir,
        env=_env(enforce=None, trust_root=False),
        capture_output=True,
        text=True,
        check=False,
    )
    # CLI prints JSON then exits non-zero on invalid.
    assert proc.stdout.strip(), (proc.stdout, proc.stderr)
    result = json.loads(proc.stdout.strip().splitlines()[-1])
    assert result["valid"] is False, result
    reason = (result.get("reason") or "").lower()
    assert "trust" in reason, result
    assert proc.returncode != 0


if __name__ == "__main__":
    test_go_dsse_verify()
    test_rust_dsse_verify()
    test_typescript_dsse_verify()
    test_cross_lang_outputs_match()
    test_unset_enforce_matches_explicit_one()
    test_go_rejects_without_trust_root_when_unset()
    print("cross-lang DSSE tests passed")
