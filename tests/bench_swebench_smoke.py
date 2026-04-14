# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Benchmark smoke suite: deterministic mode (no model calls, no network).
# Validates replay + output formatting and stable evidence generation.
# Run from repository root; CI runs this with no network/model by default.

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


# Repository root (parent of bench/)
REPO_ROOT = Path(__file__).resolve().parent.parent
RUNNER = REPO_ROOT / "bench" / "swebench" / "runner.py"
REPLAY_SCRIPT = REPO_ROOT / "bench" / "swebench" / "run_replay.py"
FIXTURES = REPO_ROOT / "tests" / "fixtures" / "bench_swebench_instances.jsonl"

# SWE-bench predictions.jsonl required keys
PREDICTIONS_KEYS = {"instance_id", "model_patch", "model_name_or_path"}

# PF metadata sidecar required keys
PFMETA_KEYS = {"instance_id", "run_id", "policy_hash", "trace_hash", "replay_bundle_hash", "cost_metrics"}

# Evidence dir expected files per instance
EVIDENCE_FILES = {"run.log", "model.patch", "metadata.json"}


def _run_runner(
    runs_dir: Path,
    out_path: Path,
    instances_file: Path,
    run_id: str = "smoke-run",
) -> tuple[int, str, str]:
    """Run bench/swebench/runner.py with --no-workspace (no network, stub engine). Returns (returncode, stdout, stderr)."""
    env = os.environ.copy()
    env["PYTHONPATH"] = str(REPO_ROOT / "bench" / "swebench")
    cmd = [
        sys.executable,
        str(RUNNER),
        "--no-workspace",
        "--instances-file", str(instances_file),
        "--runs-dir", str(runs_dir),
        "--out", str(out_path),
        "--run-id", run_id,
        "--engine", "openhands",
    ]
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    return proc.returncode, proc.stdout or "", proc.stderr or ""


def _run_replay(runs_dir: Path, run_id: str) -> tuple[int, str, str]:
    """Run bench swebench replay for the given run_id. Returns (returncode, stdout, stderr)."""
    cmd = [
        sys.executable,
        str(REPLAY_SCRIPT),
        "--run-id", run_id,
        "--runs-dir", str(runs_dir),
    ]
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
    )
    return proc.returncode, proc.stdout or "", proc.stderr or ""


def _strict_jsonl(path: Path, required_keys: set[str]) -> list[dict]:
    """Parse JSONL; require each line to be valid JSON with at least required_keys. Raises on failure."""
    lines = path.read_text(encoding="utf-8").strip().splitlines()
    out = []
    for i, line in enumerate(lines):
        if not line.strip():
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError as e:
            raise AssertionError(f"{path}: line {i+1} invalid JSON: {e}") from e
        if not isinstance(obj, dict):
            raise AssertionError(f"{path}: line {i+1} is not a JSON object")
        missing = required_keys - set(obj.keys())
        if missing:
            raise AssertionError(f"{path}: line {i+1} missing keys: {missing}")
        out.append(obj)
    return out


def test_runner_deterministic_no_network():
    """Run runner in deterministic mode (--no-workspace): no model calls, no network."""
    with tempfile.TemporaryDirectory(prefix="bench_swebench_smoke_") as tmp:
        runs_dir = Path(tmp) / "runs"
        out_path = Path(tmp) / "predictions.jsonl"
        run_id = "smoke-run"
        assert FIXTURES.exists(), f"Fixtures missing: {FIXTURES}"
        assert RUNNER.exists(), f"Runner missing: {RUNNER}"

        rc, stdout, stderr = _run_runner(runs_dir, out_path, FIXTURES, run_id=run_id)
        assert rc == 0, f"Runner failed: stdout={stdout!r} stderr={stderr!r}"

        run_dir = runs_dir / run_id
        assert run_dir.is_dir(), f"Run dir not created: {run_dir}"

        # Strict JSONL: predictions.jsonl
        assert out_path.exists(), "predictions.jsonl not created"
        preds = _strict_jsonl(out_path, PREDICTIONS_KEYS)
        assert len(preds) >= 2, "Expected at least 2 instances in predictions.jsonl"
        instance_ids = {p["instance_id"] for p in preds}
        assert "smoke-inst-1" in instance_ids and "smoke-inst-2" in instance_ids

        # PF metadata sidecar
        pfmeta = out_path.parent / (out_path.stem + ".pfmeta.jsonl")
        assert pfmeta.exists(), "predictions.pfmeta.jsonl not created"
        pfm = _strict_jsonl(pfmeta, PFMETA_KEYS)
        assert len(pfm) == len(preds), "pfmeta line count must match predictions"
        pred_ids = {p["instance_id"] for p in preds}
        pfmeta_ids = {p["instance_id"] for p in pfm}
        assert pred_ids == pfmeta_ids, "pfmeta instance_ids must match predictions"

        # Evidence per instance: run.log, model.patch, metadata.json
        for rec in preds:
            iid = rec["instance_id"]
            safe_id = "".join(c if c.isalnum() or c in "-_" else "_" for c in iid)
            inst_dir = run_dir / safe_id
            assert inst_dir.is_dir(), f"Evidence dir missing for {iid}: {inst_dir}"
            for f in EVIDENCE_FILES:
                p = inst_dir / f
                assert p.exists(), f"Evidence file missing: {p}"

        # summary.json / summary.csv (cost accounting)
        summary_json = run_dir / "summary.json"
        summary_csv = run_dir / "summary.csv"
        assert summary_json.exists(), "summary.json not created"
        assert summary_csv.exists(), "summary.csv not created"
        summary = json.loads(summary_json.read_text(encoding="utf-8"))
        assert "run_id" in summary and summary["run_id"] == run_id
        assert "instances" in summary and len(summary["instances"]) == len(preds)


def test_replay_runs_and_output_format():
    """Replay step runs without crash and produces structured output (deterministic mode may have no workspace)."""
    with tempfile.TemporaryDirectory(prefix="bench_swebench_smoke_") as tmp:
        runs_dir = Path(tmp) / "runs"
        out_path = Path(tmp) / "predictions.jsonl"
        run_id = "smoke-replay-run"
        assert FIXTURES.exists()
        rc, _, stderr = _run_runner(runs_dir, out_path, FIXTURES, run_id=run_id)
        assert rc == 0, stderr

        replay_rc, replay_stdout, replay_stderr = _run_replay(runs_dir, run_id)
        # Replay may exit 1 when repo path not found (no workspace); we only require no crash and parseable output
        assert replay_rc in (0, 1), f"Replay should exit 0 or 1: {replay_stdout} {replay_stderr}"
        # Output must mention instance or run
        combined = replay_stdout + replay_stderr
        assert "smoke-inst" in combined or "Run" in combined or "MISMATCH" in combined or "MATCH" in combined or "No instances" in combined


def test_stable_evidence_structure():
    """Two runs with same inputs produce same evidence structure (run dirs, file names, JSON keys)."""
    with tempfile.TemporaryDirectory(prefix="bench_swebench_smoke_") as tmp:
        runs_dir = Path(tmp) / "runs"
        out1 = Path(tmp) / "out1" / "predictions.jsonl"
        out1.parent.mkdir(parents=True, exist_ok=True)
        out2 = Path(tmp) / "out2" / "predictions.jsonl"
        out2.parent.mkdir(parents=True, exist_ok=True)

        rc1, _, _ = _run_runner(runs_dir, out1, FIXTURES, run_id="stable-1")
        rc2, _, _ = _run_runner(runs_dir, out2, FIXTURES, run_id="stable-2")
        assert rc1 == 0 and rc2 == 0

        run1 = runs_dir / "stable-1"
        run2 = runs_dir / "stable-2"
        assert run1.is_dir() and run2.is_dir()

        # Same instance dir names (sanitized)
        dirs1 = {d.name for d in run1.iterdir() if d.is_dir()}
        dirs2 = {d.name for d in run2.iterdir() if d.is_dir()}
        assert dirs1 == dirs2, "Evidence instance dirs should match between runs"

        # Same evidence files per instance
        for d in dirs1:
            files1 = set((run1 / d).iterdir())
            files2 = set((run2 / d).iterdir())
            names1 = {f.name for f in files1}
            names2 = {f.name for f in files2}
            assert names1 == names2, f"Instance {d}: file sets should match"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
