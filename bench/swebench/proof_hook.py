# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Proof hook: optional --prove step that builds the policy-trace Lean proof,
# produces proof.ok + proof_artifact_hash on success, structured failure on failure.
# Aligns with PF spec bundles and proof-carrying compliance.

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from bench.swebench.constants import PROOF_OK_FILENAME

PROOF_ARTIFACT_HASH_FILENAME = "proof_artifact_hash.txt"
PROOF_FAILURE_FILENAME = "proof_failure.json"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def _artifact_hash(proofs_build_dir: Path) -> Optional[str]:
    """Compute a deterministic hash over the proof build artifact (e.g. compiled lib)."""
    lake_build = proofs_build_dir / ".lake" / "build"
    if not lake_build.is_dir():
        return None
    hashes = []
    for f in sorted(lake_build.rglob("*.olean")):
        if f.is_file():
            hashes.append(f.name + " " + _sha256_file(f))
    if not hashes:
        return None
    return hashlib.sha256("\n".join(hashes).encode("utf-8")).hexdigest()


def run_proof(
    proofs_dir: Path,
    run_dir: Path,
    lake_cmd: str = "lake",
    timeout_seconds: int = 300,
) -> Tuple[bool, Optional[str], Optional[dict]]:
    """
    Run the proof step: lake build in proofs_dir.
    Returns (success, artifact_hash_if_success, failure_dict_if_failure).
    """
    proofs_dir = Path(proofs_dir).resolve()
    run_dir = Path(run_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)

    try:
        proc = subprocess.run(
            [lake_cmd, "build"],
            cwd=proofs_dir,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except FileNotFoundError:
        failure = {
            "success": False,
            "error": "lake_not_found",
            "message": f"Lake command not found: {lake_cmd}",
            "exit_code": None,
            "stdout": "",
            "stderr": "",
        }
        return False, None, failure
    except subprocess.TimeoutExpired as e:
        failure = {
            "success": False,
            "error": "timeout",
            "message": f"Proof build timed out after {timeout_seconds}s",
            "exit_code": None,
            "stdout": (e.stdout or "")[:4096] if e.stdout else "",
            "stderr": (e.stderr or "")[:4096] if e.stderr else "",
        }
        return False, None, failure
    except Exception as e:
        failure = {
            "success": False,
            "error": "exception",
            "message": str(e),
            "exit_code": None,
            "stdout": "",
            "stderr": "",
        }
        return False, None, failure

    if proc.returncode != 0:
        failure = {
            "success": False,
            "error": "build_failed",
            "message": f"Lake build exited with code {proc.returncode}",
            "exit_code": proc.returncode,
            "stdout": (proc.stdout or "")[:8192],
            "stderr": (proc.stderr or "")[:8192],
        }
        return False, None, failure

    artifact_hash = _artifact_hash(proofs_dir)
    if artifact_hash is None:
        failure = {
            "success": False,
            "error": "no_artifact",
            "message": "Build succeeded but no .olean artifacts found under .lake/build",
            "exit_code": 0,
            "stdout": (proc.stdout or "")[:2048],
            "stderr": (proc.stderr or "")[:2048],
        }
        return False, None, failure

    (run_dir / PROOF_OK_FILENAME).write_text(
        f"proof_artifact_hash={artifact_hash}\n",
        encoding="utf-8",
    )
    (run_dir / PROOF_ARTIFACT_HASH_FILENAME).write_text(
        artifact_hash + "\n",
        encoding="utf-8",
    )
    return True, artifact_hash, None


def write_proof_failure(run_dir: Path, failure: dict) -> None:
    """Write structured failure output to run_dir/proof_failure.json."""
    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / PROOF_FAILURE_FILENAME).write_text(
        json.dumps(failure, indent=2),
        encoding="utf-8",
    )
