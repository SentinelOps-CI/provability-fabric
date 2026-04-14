# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Unit tests for proof_hook: run_proof success writes proof.ok and proof_artifact_hash.txt; failure writes proof_failure.json.

from __future__ import annotations

import sys
import tempfile
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.proof_hook import (
    run_proof,
    write_proof_failure,
    PROOF_OK_FILENAME,
    PROOF_ARTIFACT_HASH_FILENAME,
    PROOF_FAILURE_FILENAME,
)
def test_run_proof_success_writes_proof_ok_and_artifact_hash():
    with tempfile.TemporaryDirectory() as td:
        run_dir = Path(td)
        proofs_dir = Path(td) / "proofs"
        proofs_dir.mkdir()
        (proofs_dir / ".lake").mkdir()
        (proofs_dir / ".lake" / "build").mkdir()
        olean = proofs_dir / ".lake" / "build" / "Foo.olean"
        olean.write_bytes(b"fake olean content")

        with mock.patch("bench.swebench.proof_hook.subprocess.run") as m_run:
            m_run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
            success, artifact_hash, failure = run_proof(proofs_dir, run_dir)

        assert success is True
        assert failure is None
        assert artifact_hash is not None
        assert (run_dir / PROOF_OK_FILENAME).exists()
        assert (run_dir / PROOF_ARTIFACT_HASH_FILENAME).exists()
        text = (run_dir / PROOF_ARTIFACT_HASH_FILENAME).read_text(encoding="utf-8").strip()
        assert text == artifact_hash


def test_run_proof_lake_not_found_returns_failure_no_proof_ok():
    with tempfile.TemporaryDirectory() as td:
        run_dir = Path(td)
        proofs_dir = Path(td) / "proofs"
        proofs_dir.mkdir()

        with mock.patch("bench.swebench.proof_hook.subprocess.run") as m_run:
            m_run.side_effect = FileNotFoundError("lake not found")
            success, artifact_hash, failure = run_proof(proofs_dir, run_dir)

        assert success is False
        assert artifact_hash is None
        assert failure is not None
        assert failure.get("error") == "lake_not_found"
        assert not (run_dir / PROOF_OK_FILENAME).exists()


def test_write_proof_failure_writes_json():
    with tempfile.TemporaryDirectory() as td:
        run_dir = Path(td)
        failure = {"success": False, "error": "timeout", "message": "timed out"}
        write_proof_failure(run_dir, failure)
        assert (run_dir / PROOF_FAILURE_FILENAME).exists()
        import json
        data = json.loads((run_dir / PROOF_FAILURE_FILENAME).read_text(encoding="utf-8"))
        assert data["error"] == "timeout"
