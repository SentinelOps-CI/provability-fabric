#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Strict 10-instance A/B gate for direct_agent (candidate) vs openhands (baseline).
# LLM is configured via env (e.g. OPENHANDS_PROVIDER=prime_intellect, PRIME_INTELLECT_API_KEY,
# OPENHANDS_MODEL=google/gemini-2.5-flash); --model forwards --openhands-model to the runner.

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
RUNNER = REPO_ROOT / "bench" / "swebench" / "runner.py"
COMPARE = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
SAMPLER = REPO_ROOT / "experiments" / "scripts" / "sample_lite_instance_ids.py"


def _run(cmd: list[str], cwd: Path, timeout_s: int) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    exe_dir = str(Path(sys.executable).resolve().parent)
    env["PATH"] = exe_dir + os.pathsep + env.get("PATH", "")
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout_s,
    )


def _extract_run_id(stdout: str) -> str:
    for line in (stdout or "").splitlines():
        if line.startswith("Run ID:"):
            return line.split(":", 1)[1].strip()
    return ""


def _load_json(path: Path, default: dict[str, Any]) -> dict[str, Any]:
    if not path.exists():
        return default
    try:
        parsed = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(parsed, dict):
            return parsed
    except (json.JSONDecodeError, OSError):
        pass
    return default


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def _phase_stdout(log_path: Path) -> str:
    try:
        return log_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _extract_instance_progress(log_text: str) -> tuple[int, int]:
    """Return (max_seen_instance_idx, declared_total_instances) from runner logs."""
    max_idx = 0
    total = 0
    for raw in (log_text or "").splitlines():
        if "Instance " not in raw or "/" not in raw:
            continue
        # Example: "... Instance 3/10: <id>"
        try:
            frag = raw.split("Instance ", 1)[1]
            lhs = frag.split(":", 1)[0].strip()
            left, right = lhs.split("/", 1)
            i = int(left.strip())
            n = int(right.strip())
        except (IndexError, ValueError):
            continue
        if i > max_idx:
            max_idx = i
        if n > total:
            total = n
    return max_idx, total


def _instances_with_critical_drop(run_dir: Path) -> list[str]:
    out: list[str] = []
    if not run_dir.exists():
        return out
    for child in run_dir.iterdir():
        if not child.is_dir():
            continue
        tr = child / "engine_trace.json"
        if not tr.exists():
            continue
        try:
            obj = json.loads(tr.read_text(encoding="utf-8"))
            report = obj.get("task_delivery_report") or {}
            if bool(report.get("critical_drop")):
                out.append(child.name)
        except (json.JSONDecodeError, OSError, AttributeError):
            continue
    return sorted(out)


def _run_watchdog(
    *,
    cmd: list[str],
    cwd: Path,
    hard_timeout_s: int,
    idle_timeout_s: int,
    progress_paths: list[Path],
    log_path: Path,
    expected_instances: int = 0,
) -> dict[str, Any]:
    """
    Run a subprocess with:
    - hard timeout (always bounded)
    - idle watchdog based on progress path mtime changes
    stdout/stderr are streamed to one log file for resumable diagnostics.
    """
    env = dict(os.environ)
    exe_dir = str(Path(sys.executable).resolve().parent)
    env["PATH"] = exe_dir + os.pathsep + env.get("PATH", "")

    log_path.parent.mkdir(parents=True, exist_ok=True)
    if log_path.exists():
        log_path.unlink()

    start = time.time()
    last_progress = start
    last_meaningful_progress = start
    last_external_mtime = 0.0
    last_log_mtime = 0.0
    last_instance_idx = 0
    for p in progress_paths:
        if p.exists():
            try:
                last_external_mtime = max(last_external_mtime, p.stat().st_mtime)
            except OSError:
                pass
    if log_path.exists():
        try:
            last_log_mtime = log_path.stat().st_mtime
        except OSError:
            pass

    watchdog_reason = ""
    with open(log_path, "w", encoding="utf-8", errors="replace") as log_f:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdout=log_f,
            stderr=subprocess.STDOUT,
            text=True,
        )
        while True:
            rc = proc.poll()
            now = time.time()
            if rc is not None:
                return {
                    "returncode": rc,
                    "elapsed_s": round(now - start, 2),
                    "watchdog_killed": False,
                    "watchdog_reason": "",
                    "log_path": str(log_path),
                }

            if now - start > hard_timeout_s:
                watchdog_reason = f"hard_timeout>{hard_timeout_s}s"
                break

            progress_tick = False
            external_progress = False
            instance_progress = False
            for p in progress_paths:
                if not p.exists():
                    continue
                try:
                    m = p.stat().st_mtime
                except OSError:
                    continue
                if m > last_external_mtime:
                    last_external_mtime = m
                    progress_tick = True
                    external_progress = True

            # Signal 1: phase log file mtime updated
            try:
                lm = log_path.stat().st_mtime
            except OSError:
                lm = 0.0
            if lm > last_log_mtime:
                last_log_mtime = lm
                progress_tick = True

            # Signal 2: instance counter advanced in logs
            if expected_instances > 0:
                text = _phase_stdout(log_path)
                instance_idx, declared_total = _extract_instance_progress(text)
                expected = declared_total if declared_total > 0 else expected_instances
                if instance_idx > last_instance_idx:
                    last_instance_idx = instance_idx
                    progress_tick = True
                    instance_progress = True

            if progress_tick:
                last_progress = now
            # Meaningful progress should reflect output growth or instance advancement,
            # not just noisy heartbeat logs from underlying tools.
            meaningful_tick = False
            if expected_instances > 0:
                meaningful_tick = external_progress or instance_progress
            elif progress_tick:
                meaningful_tick = True
            if meaningful_tick:
                last_meaningful_progress = now
            elif idle_timeout_s > 0 and (now - last_progress) > idle_timeout_s:
                watchdog_reason = f"idle_timeout>{idle_timeout_s}s"
                break
            # Extra guard for stuck phases with log churn but no actual advancement.
            if expected_instances > 0 and idle_timeout_s > 0 and (now - last_meaningful_progress) > idle_timeout_s:
                watchdog_reason = f"stalled_no_instance_advance>{idle_timeout_s}s"
                break

            time.sleep(2)

        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=10)
    return {
        "returncode": -9,
        "elapsed_s": round(time.time() - start, 2),
        "watchdog_killed": True,
        "watchdog_reason": watchdog_reason,
        "log_path": str(log_path),
    }


def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Run strict A/B gate: openhands-engine baseline vs direct_agent candidate. "
            "Set OPENHANDS_PROVIDER / API keys / OPENHANDS_MODEL (e.g. prime_intellect + Prime model id)."
        ),
    )
    ap.add_argument("--dataset", default="Lite")
    ap.add_argument("--split", default="test")
    ap.add_argument("--count", type=int, default=10)
    ap.add_argument("--instance-ids-file", default="")
    ap.add_argument("--model", default="")
    # Match bench/swebench/run_config.py defaults (openhands_timeout=1200, max_iterations=25).
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--max-iterations", type=int, default=25)
    ap.add_argument("--runs-dir", default="runs")
    ap.add_argument("--out-dir", default="runs/direct-agent-ab-gate")
    ap.add_argument("--timeout-run-s", type=int, default=36000)
    ap.add_argument("--idle-timeout-s", type=int, default=1800)
    ap.add_argument("--max-task-chars", type=int, default=12000)
    ap.add_argument("--resume", action="store_true", default=True)
    ap.add_argument("--no-resume", dest="resume", action="store_false")
    ap.add_argument(
        "--explore-compare",
        action="store_true",
        help=(
            "Run compare_runs without --require-patch-apply or --require-priced-models. "
            "Use when you want compare.json despite empty/non-applying patches (not a merge/promote gate)."
        ),
    )
    args = ap.parse_args()

    out_dir = (REPO_ROOT / args.out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    ids_file = Path(args.instance_ids_file).resolve() if args.instance_ids_file else (out_dir / "instance_ids.txt")
    checkpoint_path = out_dir / "ab_gate_checkpoint.json"
    decision_path = out_dir / "ab_gate_decision.json"
    checkpoint = _load_json(
        checkpoint_path,
        {
            "phase": "init",
            "phases": {
                "baseline": {"status": "pending"},
                "candidate": {"status": "pending"},
                "compare": {"status": "pending"},
            },
        },
    )
    if not args.resume:
        checkpoint = {
            "phase": "init",
            "phases": {
                "baseline": {"status": "pending"},
                "candidate": {"status": "pending"},
                "compare": {"status": "pending"},
            },
        }
        _write_json(checkpoint_path, checkpoint)

    # If no explicit IDs file, sample deterministic IDs once and reuse for resume.
    if not args.instance_ids_file and not ids_file.exists():
        smp = _run(
            [
                sys.executable,
                str(SAMPLER),
                "--count",
                str(args.count),
                "--seed",
                "42",
                "--out",
                str(ids_file),
            ],
            cwd=REPO_ROOT,
            timeout_s=180,
        )
        if smp.returncode != 0:
            print(smp.stdout)
            print(smp.stderr, file=sys.stderr)
            return smp.returncode

    baseline_out = out_dir / "predictions_baseline_openhands.jsonl"
    candidate_out = out_dir / "predictions_candidate_direct_agent.jsonl"

    common_args = [
        "--dataset",
        args.dataset,
        "--split",
        args.split,
        "--instance-ids-file",
        str(ids_file),
        "--openhands-timeout",
        str(args.timeout),
        "--openhands-max-iterations",
        str(args.max_iterations),
        "--runs-dir",
        args.runs_dir,
        "--verbose-instance-logs",
    ]
    if args.model:
        common_args.extend(["--openhands-model", args.model])

    t0 = time.time()
    os.environ["PF_OPENHANDS_MAX_TASK_CHARS"] = str(max(400, int(args.max_task_chars or 12000)))
    baseline_run_id = str(checkpoint.get("phases", {}).get("baseline", {}).get("run_id", "") or "")
    candidate_run_id = str(checkpoint.get("phases", {}).get("candidate", {}).get("run_id", "") or "")

    # Phase: baseline
    if checkpoint["phases"]["baseline"].get("status") != "success":
        checkpoint["phase"] = "baseline"
        checkpoint["phases"]["baseline"] = {"status": "running", "started_at": time.time()}
        _write_json(checkpoint_path, checkpoint)

        baseline_tmp = Path(str(baseline_out) + ".tmp")
        if baseline_tmp.exists():
            baseline_tmp.unlink()
        baseline_log = out_dir / "phase_baseline.log"
        base = _run_watchdog(
            cmd=[
                sys.executable,
                str(RUNNER),
                "--engine",
                "openhands",
                "--out",
                str(baseline_out),
                *common_args,
            ],
            cwd=REPO_ROOT,
            hard_timeout_s=args.timeout_run_s,
            idle_timeout_s=args.idle_timeout_s,
            progress_paths=[baseline_tmp],
            log_path=baseline_log,
            expected_instances=args.count,
        )
        base_stdout = _phase_stdout(baseline_log)
        baseline_run_id = _extract_run_id(base_stdout)
        checkpoint["phases"]["baseline"] = {
            "status": "success" if base["returncode"] == 0 and baseline_run_id else "failed",
            "run_id": baseline_run_id,
            "returncode": base["returncode"],
            "elapsed_s": base["elapsed_s"],
            "watchdog_killed": base["watchdog_killed"],
            "watchdog_reason": base["watchdog_reason"],
            "log_path": base["log_path"],
            "ended_at": time.time(),
        }
        _write_json(checkpoint_path, checkpoint)
        if checkpoint["phases"]["baseline"]["status"] != "success":
            summary = {
                "ok": False,
                "elapsed_s": round(time.time() - t0, 2),
                "baseline_run_id": baseline_run_id,
                "candidate_run_id": candidate_run_id,
                "baseline_out": str(baseline_out),
                "candidate_out": str(candidate_out),
                "compare_json": str(out_dir / "compare.json"),
                "compare_return_code": int(base["returncode"]),
                "compare_report": {},
                "failed_phase": "baseline",
                "checkpoint": str(checkpoint_path),
            }
            (out_dir / "ab_gate_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
            _write_json(decision_path, {"promotable": False, "reason": "baseline phase failed", "summary": summary})
            print(json.dumps(summary, indent=2))
            print(base_stdout)
            return int(base["returncode"])

    # Phase: candidate
    if checkpoint["phases"]["candidate"].get("status") != "success":
        checkpoint["phase"] = "candidate"
        checkpoint["phases"]["candidate"] = {"status": "running", "started_at": time.time()}
        _write_json(checkpoint_path, checkpoint)

        candidate_tmp = Path(str(candidate_out) + ".tmp")
        if candidate_tmp.exists():
            candidate_tmp.unlink()
        candidate_log = out_dir / "phase_candidate.log"
        cand = _run_watchdog(
            cmd=[
                sys.executable,
                str(RUNNER),
                "--engine",
                "direct_agent",
                "--out",
                str(candidate_out),
                *common_args,
            ],
            cwd=REPO_ROOT,
            hard_timeout_s=args.timeout_run_s,
            idle_timeout_s=args.idle_timeout_s,
            progress_paths=[candidate_tmp],
            log_path=candidate_log,
            expected_instances=args.count,
        )
        cand_stdout = _phase_stdout(candidate_log)
        candidate_run_id = _extract_run_id(cand_stdout)
        checkpoint["phases"]["candidate"] = {
            "status": "success" if cand["returncode"] == 0 and candidate_run_id else "failed",
            "run_id": candidate_run_id,
            "returncode": cand["returncode"],
            "elapsed_s": cand["elapsed_s"],
            "watchdog_killed": cand["watchdog_killed"],
            "watchdog_reason": cand["watchdog_reason"],
            "log_path": cand["log_path"],
            "ended_at": time.time(),
        }
        _write_json(checkpoint_path, checkpoint)
        if checkpoint["phases"]["candidate"]["status"] == "success":
            candidate_run_dir = (REPO_ROOT / args.runs_dir / candidate_run_id).resolve()
            critical_drop_ids = _instances_with_critical_drop(candidate_run_dir)
            if critical_drop_ids:
                checkpoint["phases"]["candidate"]["status"] = "failed"
                checkpoint["phases"]["candidate"]["returncode"] = -8
                checkpoint["phases"]["candidate"]["watchdog_reason"] = "critical_drop_guard"
                checkpoint["phases"]["candidate"]["critical_drop_instances"] = critical_drop_ids
                _write_json(checkpoint_path, checkpoint)
        if checkpoint["phases"]["candidate"]["status"] != "success":
            summary = {
                "ok": False,
                "elapsed_s": round(time.time() - t0, 2),
                "baseline_run_id": baseline_run_id,
                "candidate_run_id": candidate_run_id,
                "baseline_out": str(baseline_out),
                "candidate_out": str(candidate_out),
                "compare_json": str(out_dir / "compare.json"),
                "compare_return_code": int(cand["returncode"]),
                "compare_report": {},
                "failed_phase": "candidate",
                "checkpoint": str(checkpoint_path),
            }
            (out_dir / "ab_gate_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
            _write_json(decision_path, {"promotable": False, "reason": "candidate phase failed", "summary": summary})
            print(json.dumps(summary, indent=2))
            print(cand_stdout)
            return int(cand["returncode"])

    baseline_run_dir = (REPO_ROOT / args.runs_dir / baseline_run_id).resolve()
    candidate_run_dir = (REPO_ROOT / args.runs_dir / candidate_run_id).resolve()
    checkpoint["phase"] = "compare"
    checkpoint["phases"]["compare"] = {"status": "running", "started_at": time.time()}
    _write_json(checkpoint_path, checkpoint)
    compare_log = out_dir / "phase_compare.log"
    compare_cmd: list[str] = [
        sys.executable,
        str(COMPARE),
        "--experiment-dir",
        str(out_dir),
        "--baseline-run-dir",
        str(baseline_run_dir),
        "--pf-run-dir",
        str(candidate_run_dir),
        "--out",
        str(out_dir),
    ]
    if not args.explore_compare:
        compare_cmd.extend(["--require-patch-apply", "--require-priced-models"])
    cmp = _run_watchdog(
        cmd=compare_cmd,
        cwd=REPO_ROOT,
        hard_timeout_s=600,
        idle_timeout_s=180,
        progress_paths=[],
        log_path=compare_log,
    )
    checkpoint["phases"]["compare"] = {
        "status": "success" if cmp["returncode"] == 0 else "failed",
        "returncode": cmp["returncode"],
        "elapsed_s": cmp["elapsed_s"],
        "watchdog_killed": cmp["watchdog_killed"],
        "watchdog_reason": cmp["watchdog_reason"],
        "log_path": cmp["log_path"],
        "ended_at": time.time(),
    }
    checkpoint["phase"] = "done"
    _write_json(checkpoint_path, checkpoint)

    compare_path = out_dir / "compare.json"
    compare = {}
    if compare_path.exists():
        try:
            compare = json.loads(compare_path.read_text(encoding="utf-8"))
        except Exception:
            compare = {}

    summary = {
        "ok": bool(cmp["returncode"] == 0),
        "elapsed_s": round(time.time() - t0, 2),
        "baseline_run_id": baseline_run_id,
        "candidate_run_id": candidate_run_id,
        "baseline_out": str(baseline_out),
        "candidate_out": str(candidate_out),
        "compare_json": str(compare_path),
        "compare_return_code": cmp["returncode"],
        "compare_report": compare,
        "checkpoint": str(checkpoint_path),
    }
    (out_dir / "ab_gate_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    _write_json(
        decision_path,
        {
            "promotable": bool(cmp["returncode"] == 0 and not args.explore_compare),
            "reason": (
                "explore compare only (--explore-compare); not a strict promote gate"
                if args.explore_compare
                else ("strict gate passed" if cmp["returncode"] == 0 else "strict gate failed")
            ),
            "explore_compare": bool(args.explore_compare),
            "summary_path": str(out_dir / "ab_gate_summary.json"),
            "checkpoint_path": str(checkpoint_path),
        },
    )
    print(json.dumps(summary, indent=2))
    if cmp["returncode"] != 0:
        print(_phase_stdout(compare_log))
    return int(cmp["returncode"])


if __name__ == "__main__":
    raise SystemExit(main())

