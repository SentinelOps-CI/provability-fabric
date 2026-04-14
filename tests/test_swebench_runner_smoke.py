# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Deterministic smoke tests for the SWE-bench runner (no Hugging Face, no clone).
# Run from repository root: pytest tests/test_swebench_runner_smoke.py -v

from __future__ import annotations

import errno
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench import runner as swebench_runner_mod
from bench.swebench.util import sanitize_instance_id

RUNNER = REPO_ROOT / "bench" / "swebench" / "runner.py"
FIXTURES = REPO_ROOT / "bench" / "swebench" / "fixtures"
INSTANCES_SMOKE = FIXTURES / "instances_smoke.jsonl"
EXPECTED_INSTANCE_IDS = ("pf_smoke__1", "pf_smoke__2", "pf_smoke__3")
EXPECTED_VIOLATION_REASON = "binary_forbidden"


def _run_runner(
    instances_file: str,
    max_instances: int,
    engine: str,
    no_workspace: bool,
    out_path: str,
    runs_dir: str,
    mode: str = "default",
    policy: str = "",
    *,
    subprocess_timeout_s: int = 120,
) -> tuple[int, str, str]:
    """Run the Python runner; return (returncode, stdout, stderr)."""
    cmd = [
        sys.executable,
        str(RUNNER),
        "--instances-file", instances_file,
        "--max_instances", str(max_instances),
        "--engine", engine,
        "--out", out_path,
        "--runs-dir", runs_dir,
    ]
    if no_workspace:
        cmd.append("--no-workspace")
    if mode and mode != "default":
        cmd.extend(["--mode", mode])
    if policy:
        cmd.extend(["--policy", policy])
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=subprocess_timeout_s,
        encoding="utf-8",
        errors="replace",
    )
    return proc.returncode, proc.stdout or "", proc.stderr or ""


def _get_run_id_from_stdout(stdout: str) -> str | None:
    m = re.search(r"Run ID:\s*(\S+)", stdout)
    return m.group(1) if m else None


def _get_run_dir(runs_dir: str) -> Path | None:
    """Return the single run directory under runs_dir (the run_id subdir)."""
    p = Path(runs_dir)
    if not p.is_dir():
        return None
    subdirs = [d for d in p.iterdir() if d.is_dir() and not d.name.startswith(".")]
    return subdirs[0] if len(subdirs) == 1 else (max(subdirs, key=lambda d: d.stat().st_mtime) if subdirs else None)


@pytest.mark.skipif(not RUNNER.exists(), reason="runner.py not found (run from repo root)")
@pytest.mark.skipif(not INSTANCES_SMOKE.exists(), reason="instances_smoke.jsonl not found")
def test_a_baseline_deterministic_no_workspace(tmp_path: Path) -> None:
    """Test A: baseline, mock engine, no-workspace. Predictions + evidence per instance."""
    out = str(tmp_path / "predictions.jsonl")
    runs_dir = str(tmp_path / "pf_runs_smoke_baseline")
    rc, stdout, stderr = _run_runner(
        instances_file=str(INSTANCES_SMOKE),
        max_instances=3,
        engine="mock",
        no_workspace=True,
        out_path=out,
        runs_dir=runs_dir,
    )
    assert rc == 0, f"runner failed: stdout={stdout!r} stderr={stderr!r}"

    # predictions.jsonl has 3 lines
    pred_path = Path(out)
    assert pred_path.exists()
    lines = [s.strip() for s in pred_path.read_text(encoding="utf-8").strip().splitlines() if s.strip()]
    assert len(lines) == 3, f"expected 3 lines, got {len(lines)}"

    # each line parses as JSON with instance_id, model_patch, model_name_or_path
    for i, line in enumerate(lines):
        obj = json.loads(line)
        assert "instance_id" in obj, f"line {i+1} missing instance_id"
        assert "model_patch" in obj, f"line {i+1} missing model_patch"
        assert "model_name_or_path" in obj, f"line {i+1} missing model_name_or_path"
        assert obj["instance_id"] in EXPECTED_INSTANCE_IDS

    # evidence exists per instance: runs_dir/<run_id>/<instance_id>/metadata.json
    run_dir = _get_run_dir(runs_dir)
    assert run_dir is not None, f"expected one run dir under {runs_dir}"
    for iid in EXPECTED_INSTANCE_IDS:
        inst_dir = run_dir / sanitize_instance_id(iid)
        meta = inst_dir / "metadata.json"
        assert meta.exists(), f"missing {meta}"

    # engine_trace.json exists and has expected fields
    for iid in EXPECTED_INSTANCE_IDS:
        trace_path = run_dir / sanitize_instance_id(iid) / "engine_trace.json"
        assert trace_path.exists(), f"missing {trace_path}"
        trace = json.loads(trace_path.read_text(encoding="utf-8"))
        assert "tool_calls" in trace
        assert "prompts_sent" in trace
        assert isinstance(trace["tool_calls"], list)


@pytest.mark.skipif(not RUNNER.exists(), reason="runner.py not found (run from repo root)")
@pytest.mark.skipif(not INSTANCES_SMOKE.exists(), reason="instances_smoke.jsonl not found")
def test_b_guarded_mode_compliance_and_violations(tmp_path: Path) -> None:
    """Test B: pf_guarded mode writes compliance summary, events.jsonl, violation with reason_code, policy_hash, pfmeta."""
    out = str(tmp_path / "predictions.jsonl")
    runs_dir = str(tmp_path / "pf_runs_smoke_pf")
    rc, stdout, stderr = _run_runner(
        instances_file=str(INSTANCES_SMOKE),
        max_instances=3,
        engine="mock",
        no_workspace=True,
        out_path=out,
        runs_dir=runs_dir,
        mode="pf_guarded",
        policy="swebench_safe_v1",
        subprocess_timeout_s=300,
    )
    assert rc == 0, f"runner failed: stdout={stdout!r} stderr={stderr!r}"

    run_dir = _get_run_dir(runs_dir)
    assert run_dir is not None

    for iid in EXPECTED_INSTANCE_IDS:
        inst_dir = run_dir / sanitize_instance_id(iid)
        # policy_compliance_summary.json exists
        compliance_path = inst_dir / "policy_compliance_summary.json"
        assert compliance_path.exists(), f"missing {compliance_path}"
        compliance = json.loads(compliance_path.read_text(encoding="utf-8"))
        assert "compliant" in compliance
        assert "violations" in compliance

        # evidence/events.jsonl exists
        events_path = inst_dir / "evidence" / "events.jsonl"
        assert events_path.exists(), f"missing {events_path}"
        events = []
        for line in events_path.read_text(encoding="utf-8").strip().splitlines():
            if line.strip():
                events.append(json.loads(line))
        violations = [e for e in events if e.get("event_type") == "violation"]
        assert len(violations) >= 1, f"expected at least one violation event for {iid}"
        payload = violations[0].get("payload") or {}
        reason = payload.get("reason_code")
        assert reason == EXPECTED_VIOLATION_REASON, f"expected reason_code={EXPECTED_VIOLATION_REASON}, got {reason}"

        # metadata.json includes policy_hash
        meta_path = inst_dir / "metadata.json"
        assert meta_path.exists()
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        assert "policy_hash" in meta and meta["policy_hash"], f"missing policy_hash in {meta_path}"

    # predictions.pfmeta.jsonl exists and line-by-line instance_id matches predictions.jsonl
    pred_path = Path(out)
    pfmeta_path = pred_path.parent / (pred_path.stem + ".pfmeta.jsonl")
    assert pfmeta_path.exists(), f"missing {pfmeta_path}"
    pred_lines = [s.strip() for s in pred_path.read_text(encoding="utf-8").strip().splitlines() if s.strip()]
    pfmeta_lines = [s.strip() for s in pfmeta_path.read_text(encoding="utf-8").strip().splitlines() if s.strip()]
    assert len(pfmeta_lines) == len(pred_lines)
    for i, (pl, pm) in enumerate(zip(pred_lines, pfmeta_lines)):
        pred_obj = json.loads(pl)
        pfmeta_obj = json.loads(pm)
        assert pred_obj.get("instance_id") == pfmeta_obj.get("instance_id"), f"line {i+1} instance_id mismatch"


@pytest.mark.skipif(not RUNNER.exists(), reason="runner.py not found (run from repo root)")
@pytest.mark.skipif(not INSTANCES_SMOKE.exists(), reason="instances_smoke.jsonl not found")
def test_c_replay_roundtrip(tmp_path: Path) -> None:
    """Test C (optional): run one instance, replay, assert patch hash matches."""
    out = str(tmp_path / "predictions.jsonl")
    runs_dir = str(tmp_path / "pf_runs_replay")
    rc, stdout, stderr = _run_runner(
        instances_file=str(INSTANCES_SMOKE),
        max_instances=1,
        engine="mock",
        no_workspace=True,
        out_path=out,
        runs_dir=runs_dir,
    )
    assert rc == 0, f"runner failed: {stderr!r}"

    run_dir = _get_run_dir(runs_dir)
    assert run_dir is not None
    run_id = run_dir.name
    instance_id = EXPECTED_INSTANCE_IDS[0]
    inst_dir = run_dir / sanitize_instance_id(instance_id)

    replay_script = REPO_ROOT / "bench" / "swebench" / "run_replay.py"
    if not replay_script.exists():
        pytest.skip("run_replay.py not found")
    proc = subprocess.run(
        [
            sys.executable,
            str(replay_script),
            "--run-id", run_id,
            "--instance-id", sanitize_instance_id(instance_id),
            "--runs-dir", str(tmp_path / "pf_runs_replay"),
            "--json",
        ],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        pytest.skip(f"replay failed (workspace may be required): {proc.stderr!r}")
    out_json = json.loads(proc.stdout)
    assert out_json.get("replay_ok") or out_json.get("all_matched"), (
        f"replay did not match: {out_json}"
    )
    results = out_json.get("results") or []
    if results:
        assert results[0].get("match"), f"patch hash mismatch: {results[0]}"


@pytest.mark.skipif(not RUNNER.exists(), reason="runner.py not found (run from repo root)")
@pytest.mark.skipif(not INSTANCES_SMOKE.exists(), reason="instances_smoke.jsonl not found")
def test_d_openhands_unavailable_exits_before_run_dir(tmp_path: Path) -> None:
    """Acceptance: with --engine openhands and OpenHands unavailable, exit non-zero and create no run dir."""
    stub_dir = tmp_path / "openhands_stub"
    (stub_dir / "engines").mkdir(parents=True)
    (stub_dir / "engines" / "__init__.py").write_text("", encoding="utf-8")
    (stub_dir / "engines" / "openhands_engine.py").write_text(
        'raise ImportError("openhands not available for test")\n',
        encoding="utf-8",
    )
    out_path = str(tmp_path / "predictions.jsonl")
    runs_dir = str(tmp_path / "runs")
    runner_args = [
        "--instances-file", str(INSTANCES_SMOKE),
        "--max_instances", "1",
        "--engine", "openhands",
        "--no-workspace",
        "--out", out_path,
        "--runs-dir", runs_dir,
    ]
    # Run via launcher so stub_dir is sys.path[0]; otherwise script dir (bench/swebench) wins and real engine loads.
    bench_swebench = RUNNER.parent
    launcher = (
        "import sys, runpy\n"
        "sys.path.insert(0, %r)\n"
        "sys.path.insert(1, %r)\n"
        "sys.argv = [%r] + %r\n"
        "runpy.run_path(%r, run_name='__main__')\n"
    ) % (str(stub_dir), str(bench_swebench), str(RUNNER), runner_args, str(RUNNER))
    cmd = [sys.executable, "-c", launcher]
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode != 0, (
        "expected non-zero exit when OpenHands unavailable; stdout=%r stderr=%r"
        % (proc.stdout, proc.stderr)
    )
    run_root = Path(runs_dir)
    if run_root.exists():
        subdirs = [d for d in run_root.iterdir() if d.is_dir()]
        assert len(subdirs) == 0, (
            "expected no run_id subdir when OpenHands unavailable; found %s" % subdirs
        )


@pytest.mark.skipif(not RUNNER.exists(), reason="runner.py not found (run from repo root)")
@pytest.mark.skipif(not INSTANCES_SMOKE.exists(), reason="instances_smoke.jsonl not found")
def test_e_guarded_evidence_unconditional_when_engine_raises(tmp_path: Path) -> None:
    """Acceptance: when the engine raises, evidence/ and policy_compliance_summary.json and metadata.json are still written."""
    crash_stub = tmp_path / "crash_engine_stub"
    (crash_stub / "engines").mkdir(parents=True)
    (crash_stub / "engines" / "__init__.py").write_text("", encoding="utf-8")
    (crash_stub / "engines" / "mock_engine.py").write_text(
        'def solve(*args, **kwargs):\n    raise RuntimeError("acceptance test: engine crash")\n',
        encoding="utf-8",
    )
    out_path = str(tmp_path / "predictions.jsonl")
    runs_dir = str(tmp_path / "runs_crash_test")
    bench_swebench = str(REPO_ROOT / "bench" / "swebench")
    launcher = tmp_path / "run_runner_with_stub.py"
    launcher.write_text(
        "import sys\n"
        "sys.path.insert(0, %(bench)r)\n"
        "sys.path.insert(0, %(stub)r)\n"
        "sys.argv = ['runner.py'] + sys.argv[1:]\n"
        "import runner\n"
        "runner.main()\n"
        % {"stub": str(crash_stub), "bench": bench_swebench},
        encoding="utf-8",
    )
    cmd = [
        sys.executable,
        str(launcher),
        "--instances-file", str(INSTANCES_SMOKE),
        "--max_instances", "1",
        "--engine", "mock",
        "--mode", "pf_guarded",
        "--policy", "swebench_safe_v1",
        "--no-workspace",
        "--out", out_path,
        "--runs-dir", runs_dir,
    ]
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, (
        "runner must complete (record failure per instance); stderr=%s" % (proc.stderr or "")
    )
    run_dir = _get_run_dir(runs_dir)
    assert run_dir is not None, "expected one run dir under %s" % runs_dir
    instance_id = EXPECTED_INSTANCE_IDS[0]
    inst_dir = run_dir / sanitize_instance_id(instance_id)
    assert inst_dir.is_dir(), "expected instance dir %s" % inst_dir

    events_path = inst_dir / "evidence" / "events.jsonl"
    assert events_path.exists(), "evidence/events.jsonl must exist even when engine raises"
    events_content = events_path.read_text(encoding="utf-8").strip()
    assert len(events_content) > 0, "at least one event (run_started)"
    events_lines = [ln for ln in events_content.splitlines() if ln.strip()]
    assert len(events_lines) >= 1, "events.jsonl must contain at least one event"

    compliance_path = inst_dir / "policy_compliance_summary.json"
    assert compliance_path.exists(), "policy_compliance_summary.json must exist even when engine raises"

    meta_path = inst_dir / "metadata.json"
    assert meta_path.exists(), "metadata.json must exist"
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    assert meta.get("engine_success") is False, "metadata must record engine_success=false when engine raised"


def test_stderr_helpers_ignore_broken_pipe() -> None:
    """_stderr_write_safe / _eprint / _log must not raise when stderr is a broken pipe."""

    class BrokenPipeStderr:
        def write(self, _s: str) -> int:
            raise BrokenPipeError()

        def flush(self) -> None:
            pass

    class EPIPEStderr:
        def write(self, _s: str) -> int:
            raise OSError(errno.EPIPE, "broken pipe")

        def flush(self) -> None:
            pass

    old_stderr = sys.stderr
    old_quiet = os.environ.get("PF_SWEBENCH_QUIET")
    try:
        os.environ.pop("PF_SWEBENCH_QUIET", None)
        sys.stderr = BrokenPipeStderr()
        swebench_runner_mod._stderr_write_safe("x")
        swebench_runner_mod._eprint("y")
        swebench_runner_mod._log("z")
        sys.stderr = EPIPEStderr()
        swebench_runner_mod._stderr_write_safe("x")
        swebench_runner_mod._eprint("y")
        swebench_runner_mod._log("z")
    finally:
        sys.stderr = old_stderr
        if old_quiet is None:
            os.environ.pop("PF_SWEBENCH_QUIET", None)
        else:
            os.environ["PF_SWEBENCH_QUIET"] = old_quiet
