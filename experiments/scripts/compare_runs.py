#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Aggregator: baseline/eval/*, pf/eval/*, PF run summary/cost/compliance ->
# compare.json and compare.csv (one command, reproducible).

from __future__ import annotations

import argparse
import csv
import json
import statistics
import sys
from datetime import datetime, timezone
from collections import Counter
from pathlib import Path
from typing import Any

# Ensure repo root on path for bench.swebench and experiments
_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from experiments.harness_report import (  # noqa: E402
    RESOLVED_IDS,
    find_run_report,
    load_run_report,
)
from experiments.run_evidence import (  # noqa: E402
    load_compliance,
    load_cost_report,
    load_patch_apply_check,
    load_summary,
    load_timing,
    has_proof_ok,
    has_replay_bundle,
)
from bench.swebench.constants import COMPLIANCE_FILENAME

TOTAL_INSTANCES = "total_instances"
PATCH_APPLY_ERRORS_TOP_N = 10

BUDGET_KEYS = ("timeout_sec", "max_steps", "max_tool_calls")
MODEL_KEYS = ("model", "model_params")


def _percentile_sorted(sorted_vals: list[float], p: float) -> float | None:
    """p in [0,100]. sorted_vals must be non-empty sorted list."""
    if not sorted_vals:
        return None
    n = len(sorted_vals)
    if n == 1:
        return round(sorted_vals[0], 4)
    idx = min(max(int(round((p / 100.0) * (n - 1))), 0), n - 1)
    return round(sorted_vals[idx], 4)


def _distribution_stats(vals: list[float]) -> dict[str, Any] | None:
    if not vals:
        return None
    s = sorted(vals)
    n = len(s)
    return {
        "mean": round(sum(s) / n, 4),
        "median": round(statistics.median(s), 4),
        "p90": _percentile_sorted(s, 90.0),
        "p95": _percentile_sorted(s, 95.0),
        "n": n,
    }


def _collect_run_attempt_metrics(run_dir: Path | None) -> dict[str, Any]:
    """Per-attempt cost, latency/tokens distributions, termination mix (all instances in summary)."""
    out: dict[str, Any] = {}
    if not run_dir or not run_dir.exists():
        return out
    summary = load_summary(run_dir)
    if not summary:
        return out
    instances = summary.get("instances") or []
    iids = [rec.get("instance_id") for rec in instances if rec.get("instance_id")]
    if not iids:
        return out

    pt_sum = ct_sum = wc_sum = tc_sum = iter_sum = 0.0
    n_cost = 0
    walls: list[float] = []
    tokens: list[float] = []
    tcalls: list[float] = []
    iters: list[float] = []
    term_reasons: Counter[str] = Counter()
    max_steps_true = max_steps_false = 0
    timeout_true = timeout_false = 0
    n_timing = 0
    model_name = ""

    for iid in iids:
        cr = load_cost_report(run_dir, iid)
        tm = load_timing(run_dir, iid)
        if cr:
            pt = int(cr.get("prompt_tokens") or 0)
            ct = int(cr.get("completion_tokens") or 0)
            pt_sum += pt
            ct_sum += ct
            wc_sum += float(cr.get("wall_clock_s") or 0)
            tc_sum += int(cr.get("tool_calls") or 0)
            itv = int(cr.get("iterations") or 0)
            iter_sum += itv
            n_cost += 1
            tokens.append(float(pt + ct))
            tcalls.append(float(cr.get("tool_calls") or 0))
            iters.append(float(itv))
            if not model_name and (cr.get("model_name") or "").strip():
                model_name = str(cr.get("model_name")).strip()
        wall: float | None = None
        if tm is not None and tm.get("wall_clock_s") is not None:
            wall = float(tm["wall_clock_s"])
        elif cr is not None:
            wall = float(cr.get("wall_clock_s") or 0)
        if wall is not None:
            walls.append(wall)
        if tm is not None:
            n_timing += 1
            tr = tm.get("termination_reason")
            term_reasons[str(tr).strip() if tr is not None else "(missing)"] += 1
            if tm.get("max_steps_reached"):
                max_steps_true += 1
            else:
                max_steps_false += 1
            if tm.get("timeout_reached"):
                timeout_true += 1
            else:
                timeout_false += 1

    if n_cost:
        out["cost_per_attempt"] = {
            "prompt_tokens": round(pt_sum / n_cost, 2),
            "completion_tokens": round(ct_sum / n_cost, 2),
            "wall_clock_s": round(wc_sum / n_cost, 4),
            "tool_calls": round(tc_sum / n_cost, 2),
            "iterations": round(iter_sum / n_cost, 2),
            "n": int(n_cost),
        }
    out["latency_per_attempt"] = _distribution_stats(walls)
    out["tokens_per_attempt"] = _distribution_stats(tokens)
    out["tool_calls_per_attempt"] = _distribution_stats(tcalls)
    out["iterations_per_attempt"] = _distribution_stats(iters)
    tmix: dict[str, Any] = {
        "n_with_timing": n_timing,
        "termination_reason_counts": dict(term_reasons.most_common(25)),
        "max_steps_reached_count": max_steps_true,
        "max_steps_not_reached_count": max_steps_false,
        "timeout_reached_count": timeout_true,
        "timeout_not_reached_count": timeout_false,
    }
    denom = max_steps_true + max_steps_false
    if denom > 0:
        tmix["max_steps_reached_rate"] = round(max_steps_true / denom, 6)
        tmix["timeout_reached_rate"] = round(timeout_true / denom, 6)
    out["termination_mix"] = tmix
    if model_name:
        out["model_name_observed"] = model_name
    return out


def _load_run_manifest(run_dir: Path) -> dict[str, Any] | None:
    """Load experiment_manifest.json from run dir if present."""
    path = run_dir / "experiment_manifest.json"
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def _budget_slice(manifest: dict[str, Any]) -> dict[str, Any]:
    """Extract comparable budget and model fields for drift check."""
    out: dict[str, Any] = {}
    budgets = manifest.get("budgets") or {}
    for k in BUDGET_KEYS:
        out[k] = budgets.get(k)
    for k in MODEL_KEYS:
        out[k] = manifest.get(k)
    return out


def aggregate(
    baseline_eval_dir: Path,
    pf_eval_dir: Path,
    baseline_run_dir: Path | None,
    pf_run_dir: Path | None,
) -> dict[str, Any]:
    out: dict[str, Any] = {
        "baseline": {"solve_rate": None, "cost_per_solved": None},
        "pf": {
            "solve_rate": None,
            "cost_per_solved": None,
            "policy_violation_rate_all": None,
            "policy_violation_rate_final": None,
            "replay_available": None,
            "replay_success_rate": None,
        },
        "delta": {"solve_rate": None},
        "violation_reasons_top10": [],
        "patch_apply": {
            "total": 0,
            "applies_true": 0,
            "applies_false": 0,
            "errors_topN": [],
        },
    }

    # Harness: baseline
    baseline_resolved: set[str] = set()
    baseline_total = 0
    br_path = find_run_report(baseline_eval_dir)
    br: dict[str, Any] | None = None
    if br_path:
        br = load_run_report(br_path)
        if br:
            baseline_resolved = set(br.get(RESOLVED_IDS, []))
            baseline_total = br.get(TOTAL_INSTANCES) or len(baseline_resolved) + len(br.get("unresolved_ids", [])) + len(br.get("error_ids", [])) + len(br.get("empty_patch_ids", []))
    if baseline_total > 0:
        out["baseline"]["solve_rate"] = round(len(baseline_resolved) / baseline_total, 6)

    # Harness: PF
    pf_resolved: set[str] = set()
    pf_total = 0
    pr_path = find_run_report(pf_eval_dir)
    pr: dict[str, Any] | None = None
    if pr_path:
        pr = load_run_report(pr_path)
        if pr:
            pf_resolved = set(pr.get(RESOLVED_IDS, []))
            pf_total = pr.get(TOTAL_INSTANCES) or len(pf_resolved) + len(pr.get("unresolved_ids", [])) + len(pr.get("error_ids", [])) + len(pr.get("empty_patch_ids", []))
    if pf_total > 0:
        out["pf"]["solve_rate"] = round(len(pf_resolved) / pf_total, 6)

    if out["baseline"]["solve_rate"] is not None and out["pf"]["solve_rate"] is not None:
        out["delta"]["solve_rate"] = round(out["pf"]["solve_rate"] - out["baseline"]["solve_rate"], 6)

    # Instance IDs from harness reports (for patch_apply fallback when summary has no instances).
    all_report_instance_ids: set[str] = set()
    for report in (br, pr):
        if report:
            all_report_instance_ids.update(report.get(RESOLVED_IDS, []) or [])
            all_report_instance_ids.update(report.get("unresolved_ids", []) or [])
            all_report_instance_ids.update(report.get("error_ids", []) or [])
            all_report_instance_ids.update(report.get("empty_patch_ids", []) or [])

    # Cost per solved (tokens + wall_clock + tool_calls)
    def cost_per_solved(run_dir: Path, resolved_ids: set[str]) -> dict[str, float] | None:
        if not run_dir or not run_dir.exists() or not resolved_ids:
            return None
        summary = load_summary(run_dir)
        if not summary:
            return None
        instances = summary.get("instances") or []
        by_id = {rec.get("instance_id"): rec for rec in instances if rec.get("instance_id")}
        prompt_tokens = completion_tokens = wall_clock_s = tool_calls = 0.0
        n = 0
        for iid in resolved_ids:
            rec = by_id.get(iid) or load_cost_report(run_dir, iid)
            if not rec:
                continue
            n += 1
            prompt_tokens += int(rec.get("prompt_tokens") or 0)
            completion_tokens += int(rec.get("completion_tokens") or 0)
            wall_clock_s += float(rec.get("wall_clock_s") or 0)
            tool_calls += int(rec.get("tool_calls") or 0)
        if n == 0:
            return None
        return {
            "prompt_tokens": round(prompt_tokens / n, 2),
            "completion_tokens": round(completion_tokens / n, 2),
            "wall_clock_s": round(wall_clock_s / n, 2),
            "tool_calls": round(tool_calls / n, 2),
            "n_solved": n,
        }

    out["baseline"]["cost_per_solved"] = cost_per_solved(baseline_run_dir, baseline_resolved) if baseline_run_dir else None
    out["pf"]["cost_per_solved"] = cost_per_solved(pf_run_dir, pf_resolved) if pf_run_dir else None

    if baseline_run_dir:
        for k, v in _collect_run_attempt_metrics(baseline_run_dir).items():
            out["baseline"][k] = v
    if pf_run_dir:
        for k, v in _collect_run_attempt_metrics(pf_run_dir).items():
            out["pf"][k] = v

    from experiments.scripts.model_pricing import build_estimated_cost_usd_block

    out["estimated_cost_usd"] = build_estimated_cost_usd_block(baseline_run_dir, pf_run_dir)

    # PF policy violation rate (all attempts; and on final accepted patch)
    if pf_run_dir and pf_run_dir.exists():
        summary = load_summary(pf_run_dir)
        instances = (summary or {}).get("instances") or []
        all_tool_calls = 0
        all_violations = 0
        final_tool_calls = 0
        final_violations = 0
        reason_counter: Counter[str] = Counter()
        for rec in instances:
            iid = rec.get("instance_id")
            if not iid:
                continue
            comp = load_compliance(pf_run_dir, iid)
            if not comp:
                continue
            tc = int(comp.get("total_tool_calls") or 0)
            v = int(comp.get("violations") or 0)
            all_tool_calls += tc
            all_violations += v
            for r in comp.get("reason_codes") or []:
                reason_counter[r] += 1
            if iid in pf_resolved:
                final_tool_calls += tc
                final_violations += v
        if all_tool_calls > 0:
            out["pf"]["policy_violation_rate_all"] = round(all_violations / all_tool_calls, 6)
        if final_tool_calls > 0:
            out["pf"]["policy_violation_rate_final"] = round(final_violations / final_tool_calls, 6)
        out["violation_reasons_top10"] = [{"reason_code": r, "count": c} for r, c in reason_counter.most_common(10)]

        # Policy section for compare.json: reason_codes, denied_commands (from violation_details)
        denied_cmd_counter: Counter[str] = Counter()
        for rec in instances:
            iid = rec.get("instance_id")
            if not iid:
                continue
            comp = load_compliance(pf_run_dir, iid)
            if not comp:
                continue
            for detail in comp.get("violation_details") or []:
                payload = detail.get("payload") or {}
                cmd = payload.get("command_or_path") or payload.get("command") or ""
                if cmd:
                    snippet = (cmd[:120] + "..." if len(cmd) > 120 else cmd).strip()
                    denied_cmd_counter[snippet] += 1
        out["policy"] = {
            "reason_codes_topN": [{"reason_code": r, "count": c} for r, c in reason_counter.most_common(10)],
            "denied_commands_topN": [{"command_snippet": s, "count": c} for s, c in denied_cmd_counter.most_common(10)],
            "commands_seen_topN": [],  # Reserved: would require recording allowed commands in evidence
        }

        # Denial recovery: denials_total_pf, episodes_aborted_after_denial_pf, recovered_after_denial_pf_rate
        denials_total_pf = 0
        episodes_aborted_after_denial_pf = 0
        recovered_after_denial_pf = 0
        for rec in instances:
            iid = rec.get("instance_id")
            if not iid:
                continue
            comp = load_compliance(pf_run_dir, iid)
            if not comp:
                continue
            violations = int(comp.get("violations") or comp.get("total_violations") or 0)
            if violations == 0:
                continue
            denials_total_pf += violations
            pac = load_patch_apply_check(pf_run_dir, iid)
            empty_reason = (pac or {}).get("empty_patch_reason")
            if empty_reason == "guard_denial_prevented_writes":
                episodes_aborted_after_denial_pf += 1
            else:
                recovered_after_denial_pf += 1
        out["pf"]["denials_total_pf"] = denials_total_pf
        out["pf"]["episodes_aborted_after_denial_pf"] = episodes_aborted_after_denial_pf
        denom = recovered_after_denial_pf + episodes_aborted_after_denial_pf
        out["pf"]["recovered_after_denial_pf_rate"] = (
            round(recovered_after_denial_pf / denom, 6) if denom > 0 else None
        )

        # Replay: only set success_rate when at least one bundle exists; otherwise available=false, success_rate=null
        if instances:
            with_bundle = sum(1 for rec in instances if has_replay_bundle(pf_run_dir, rec.get("instance_id") or ""))
            if with_bundle == 0:
                out["pf"]["replay_available"] = False
                out["pf"]["replay_success_rate"] = None
            else:
                out["pf"]["replay_available"] = True
                out["pf"]["replay_success_rate"] = round(with_bundle / len(instances), 6)

    # Patch-apply aggregation from both run dirs (patch_apply_check.json per instance)
    stderr_bucket_counter: Counter[str] = Counter()
    empty_patch_reason_counter: Counter[str] = Counter()
    for run_dir in (baseline_run_dir, pf_run_dir):
        if not run_dir or not run_dir.exists():
            continue
        summary = load_summary(run_dir)
        instances = (summary or {}).get("instances") or []
        if not instances and all_report_instance_ids:
            instances = [{"instance_id": iid} for iid in sorted(all_report_instance_ids)]
        for rec in instances:
            iid = rec.get("instance_id")
            if not iid:
                continue
            pac = load_patch_apply_check(run_dir, iid)
            if not pac:
                continue
            out["patch_apply"]["total"] += 1
            applies = pac.get("applies")
            if applies is True:
                out["patch_apply"]["applies_true"] += 1
            else:
                out["patch_apply"]["applies_false"] += 1
                stderr = (pac.get("stderr") or "").strip()
                bucket = stderr[:200] if len(stderr) > 200 else stderr or "(no stderr)"
                stderr_bucket_counter[bucket] += 1
            reason = pac.get("empty_patch_reason")
            if reason:
                empty_patch_reason_counter[reason] += 1
    out["patch_apply"]["errors_topN"] = [
        {"stderr": s, "count": c}
        for s, c in stderr_bucket_counter.most_common(PATCH_APPLY_ERRORS_TOP_N)
    ]
    out["empty_patch_reasons_topN"] = [
        {"reason": r, "count": c}
        for r, c in empty_patch_reason_counter.most_common(10)
    ]

    # Env drift when both run dirs exist
    if baseline_run_dir and baseline_run_dir.exists() and pf_run_dir and pf_run_dir.exists():
        baseline_env: dict[str, Any] = {}
        pf_env: dict[str, Any] = {}
        for run_dir, env_dict in ((baseline_run_dir, baseline_env), (pf_run_dir, pf_env)):
            env_path = run_dir / "env.json"
            if env_path.exists():
                try:
                    env_dict.update(json.loads(env_path.read_text(encoding="utf-8")))
                except (json.JSONDecodeError, OSError):
                    pass
        drift: dict[str, Any] = {}
        if baseline_env and pf_env:
            for key in set(baseline_env) | set(pf_env):
                if baseline_env.get(key) != pf_env.get(key):
                    drift[key] = {"baseline": baseline_env.get(key), "pf": pf_env.get(key)}
            if drift:
                out["env_drift"] = drift
            else:
                out["env_drift"] = {"pip_freeze_hash_match": baseline_env.get("pip_freeze_hash") == pf_env.get("pip_freeze_hash")}

    # Reproducibility: dataset and versions from eval_metadata and env.json
    for eval_dir in (baseline_eval_dir, pf_eval_dir):
        meta_path = eval_dir / "eval_metadata.json"
        if meta_path.exists():
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
                if out.get("dataset_name") is None and meta.get("dataset_name"):
                    out["dataset_name"] = meta["dataset_name"]
                if out.get("split") is None and meta.get("split"):
                    out["split"] = meta["split"]
                if out.get("datasets_version") is None and meta.get("datasets_version") is not None:
                    out["datasets_version"] = meta["datasets_version"]
                if out.get("swebench_version") is None and meta.get("swebench_version") is not None:
                    out["swebench_version"] = meta["swebench_version"]
                if out.get("harness_dataset_id") is None and meta.get("harness_dataset_id"):
                    out["harness_dataset_id"] = meta["harness_dataset_id"]
            except (json.JSONDecodeError, OSError):
                pass

    for run_dir in (baseline_run_dir, pf_run_dir):
        if not run_dir or not run_dir.exists():
            continue
        env_path = run_dir / "env.json"
        if env_path.exists() and out.get("openhands_version") is None:
            try:
                env = json.loads(env_path.read_text(encoding="utf-8"))
                if env.get("openhands_version") is not None:
                    out["openhands_version"] = env["openhands_version"]
                    break
            except (json.JSONDecodeError, OSError):
                pass

    from experiments.scripts.harness_eval_timing import summarize_harness_eval_from_eval_dir

    harness_baseline = summarize_harness_eval_from_eval_dir(baseline_eval_dir)
    harness_pf = summarize_harness_eval_from_eval_dir(pf_eval_dir)
    harness_baseline["n_instances_in_report"] = baseline_total if baseline_total > 0 else None
    harness_pf["n_instances_in_report"] = pf_total if pf_total > 0 else None
    out["harness_eval"] = {"baseline": harness_baseline, "pf": harness_pf}

    return out


def build_metrics_full(report: dict[str, Any], experiment_id: str) -> dict[str, Any]:
    """Single run-card JSON alongside compare.json (subset + harness + pins pointer)."""
    b = report.get("baseline") or {}
    p = report.get("pf") or {}
    d = report.get("delta") or {}
    return {
        "schema_version": "metrics_full/1.0",
        "experiment_id": experiment_id,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "solve_rates": {
            "baseline": b.get("solve_rate"),
            "pf": p.get("solve_rate"),
            "delta": d.get("solve_rate"),
        },
        "harness_eval": report.get("harness_eval"),
        "agent_latency_per_attempt": {
            "baseline": b.get("latency_per_attempt"),
            "pf": p.get("latency_per_attempt"),
        },
        "estimated_cost_usd": report.get("estimated_cost_usd"),
        "version_pins_observed": {
            "openhands_version": report.get("openhands_version"),
            "datasets_version": report.get("datasets_version"),
            "swebench_version": report.get("swebench_version"),
            "harness_dataset_id": report.get("harness_dataset_id"),
        },
        "repro_note": (
            "Pin OpenHands, Docker images, and pip in env.json / experiment manifest after a green run; "
            "long runs can fail on API or version drift."
        ),
    }


def build_csv_rows(
    baseline_eval_dir: Path,
    pf_eval_dir: Path,
    baseline_run_dir: Path | None,
    pf_run_dir: Path | None,
    report: dict[str, Any],
) -> list[dict[str, Any]]:
    """Per-instance and summary rows for compare.csv (pivot-friendly)."""
    rows: list[dict[str, Any]] = []

    br_path = find_run_report(baseline_eval_dir)
    pr_path = find_run_report(pf_eval_dir)
    br = load_run_report(br_path) if br_path else None
    pr = load_run_report(pr_path) if pr_path else None
    baseline_resolved = set(br.get(RESOLVED_IDS, [])) if br else set()
    pf_resolved = set(pr.get(RESOLVED_IDS, [])) if pr else set()
    all_ids = sorted(baseline_resolved | pf_resolved)
    if br:
        for iid in set(br.get("resolved_ids", []) + br.get("unresolved_ids", []) + br.get("error_ids", []) + br.get("empty_patch_ids", [])):
            all_ids.append(iid)
    if pr:
        for iid in set(pr.get("resolved_ids", []) + pr.get("unresolved_ids", []) + pr.get("error_ids", []) + pr.get("empty_patch_ids", [])):
            all_ids.append(iid)
    if not all_ids and (baseline_run_dir or pf_run_dir):
        for run_dir in (baseline_run_dir, pf_run_dir):
            if not run_dir:
                continue
            summary = load_summary(run_dir)
            if summary:
                for rec in summary.get("instances") or []:
                    iid = rec.get("instance_id")
                    if iid:
                        all_ids.append(iid)
    all_ids = sorted(set(all_ids))

    for iid in all_ids:
        row = {
            "instance_id": iid,
            "baseline_resolved": 1 if iid in baseline_resolved else 0,
            "pf_resolved": 1 if iid in pf_resolved else 0,
        }
        if baseline_run_dir:
            cr = load_cost_report(baseline_run_dir, iid)
            pac = load_patch_apply_check(baseline_run_dir, iid)
            if cr:
                row["baseline_prompt_tokens"] = cr.get("prompt_tokens")
                row["baseline_completion_tokens"] = cr.get("completion_tokens")
                row["baseline_wall_clock_s"] = cr.get("wall_clock_s")
                row["baseline_tool_calls"] = cr.get("tool_calls")
            if pac is not None:
                row["baseline_patch_applies"] = bool(pac.get("applies"))
        if pf_run_dir:
            cr = load_cost_report(pf_run_dir, iid)
            comp = load_compliance(pf_run_dir, iid)
            pac = load_patch_apply_check(pf_run_dir, iid)
            if cr:
                row["pf_prompt_tokens"] = cr.get("prompt_tokens")
                row["pf_completion_tokens"] = cr.get("completion_tokens")
                row["pf_wall_clock_s"] = cr.get("wall_clock_s")
                row["pf_tool_calls"] = cr.get("tool_calls")
            if comp:
                row["pf_violations"] = comp.get("violations")
                row["pf_total_tool_calls"] = comp.get("total_tool_calls")
            if pac is not None:
                row["pf_patch_applies"] = bool(pac.get("applies"))
        rows.append(row)

    # Summary row
    summary_row = {"instance_id": "_summary"}
    b = report.get("baseline") or {}
    p = report.get("pf") or {}
    summary_row["baseline_solve_rate"] = b.get("solve_rate")
    summary_row["pf_solve_rate"] = p.get("solve_rate")
    summary_row["delta_solve_rate"] = (report.get("delta") or {}).get("solve_rate")
    if b.get("cost_per_solved"):
        summary_row["baseline_cost_tokens_avg"] = (b["cost_per_solved"].get("prompt_tokens") or 0) + (b["cost_per_solved"].get("completion_tokens") or 0)
        summary_row["baseline_cost_wall_clock_avg"] = b["cost_per_solved"].get("wall_clock_s")
        summary_row["baseline_cost_tool_calls_avg"] = b["cost_per_solved"].get("tool_calls")
    if p.get("cost_per_solved"):
        summary_row["pf_cost_tokens_avg"] = (p["cost_per_solved"].get("prompt_tokens") or 0) + (p["cost_per_solved"].get("completion_tokens") or 0)
        summary_row["pf_cost_wall_clock_avg"] = p["cost_per_solved"].get("wall_clock_s")
        summary_row["pf_cost_tool_calls_avg"] = p["cost_per_solved"].get("tool_calls")
    summary_row["pf_policy_violation_rate_all"] = p.get("policy_violation_rate_all")
    summary_row["pf_policy_violation_rate_final"] = p.get("policy_violation_rate_final")
    summary_row["pf_replay_available"] = p.get("replay_available")
    summary_row["pf_replay_success_rate"] = p.get("replay_success_rate")
    pa = report.get("patch_apply") or {}
    summary_row["patch_apply_total"] = pa.get("total")
    summary_row["patch_apply_applies_true"] = pa.get("applies_true")
    summary_row["patch_apply_applies_false"] = pa.get("applies_false")
    rows.append(summary_row)
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Produce comparison report (compare.json + compare.csv) from baseline/pf eval and PF run dirs.",
    )
    parser.add_argument(
        "--experiment-dir",
        type=str,
        default="runs/exp-step2-lite-smoke",
        help="Experiment directory containing baseline/eval and pf/eval; output written here",
    )
    parser.add_argument(
        "--baseline-eval-dir",
        type=str,
        default="",
        help="Override baseline eval dir (default: <experiment-dir>/baseline/eval)",
    )
    parser.add_argument(
        "--pf-eval-dir",
        type=str,
        default="",
        help="Override PF eval dir (default: <experiment-dir>/pf/eval)",
    )
    parser.add_argument(
        "--baseline-run-dir",
        type=str,
        default="",
        help="PF run dir for baseline (runs/<run_id>) for cost_per_solved; optional",
    )
    parser.add_argument(
        "--pf-run-dir",
        type=str,
        default="",
        help="PF run dir for PF run (runs/<run_id>) for cost, compliance, replay; required for full report",
    )
    parser.add_argument(
        "--out",
        type=str,
        default="",
        help="Output directory for compare.json and compare.csv (default: experiment-dir)",
    )
    parser.add_argument(
        "--require-harness",
        action="store_true",
        help="Exit with error unless baseline and PF eval reports exist and yield non-null solve rates",
    )
    parser.add_argument(
        "--require-compliance",
        action="store_true",
        help="Exit with error unless every PF instance has policy_compliance_summary.json",
    )
    parser.add_argument(
        "--require-patch-apply",
        action="store_true",
        help="Exit with error unless patch_apply.applies_false == 0 (required for Step 2 parity; fix patch extraction/apply before interpreting solve rates)",
    )
    parser.add_argument(
        "--require-priced-models",
        action="store_true",
        help="Exit with error if estimated_cost_usd has token totals but model not in model_pricing USD_PER_1M",
    )
    args = parser.parse_args()

    exp_dir = Path(args.experiment_dir)
    baseline_eval = Path(args.baseline_eval_dir or str(exp_dir / "baseline" / "eval"))
    pf_eval = Path(args.pf_eval_dir or str(exp_dir / "pf" / "eval"))
    baseline_run = Path(args.baseline_run_dir) if args.baseline_run_dir else None
    pf_run = Path(args.pf_run_dir) if args.pf_run_dir else None
    out_dir = Path(args.out or str(exp_dir))
    out_dir.mkdir(parents=True, exist_ok=True)

    report = aggregate(baseline_eval, pf_eval, baseline_run, pf_run)

    # Replay section: merge replay_summary.json if present (from run_replay_sample.py)
    replay_summary_path = out_dir / "replay_summary.json"
    if replay_summary_path.exists():
        try:
            replay_data = json.loads(replay_summary_path.read_text(encoding="utf-8"))
            report["replay"] = {
                "sample_size": replay_data.get("sample_size"),
                "success_rate": replay_data.get("success_rate"),
                "mismatch_count": replay_data.get("mismatch_count"),
                "replay_fail_reasons_topN": replay_data.get("replay_fail_reasons_topN", []),
            }
        except (json.JSONDecodeError, OSError):
            pass

    exit_code = 0

    if args.require_harness:
        br_path = find_run_report(baseline_eval)
        pr_path = find_run_report(pf_eval)
        if not br_path or not br_path.exists():
            print("Error: --require-harness: baseline eval report not found in %s" % baseline_eval, file=sys.stderr)
            exit_code = 1
        elif not pr_path or not pr_path.exists():
            print("Error: --require-harness: PF eval report not found in %s" % pf_eval, file=sys.stderr)
            exit_code = 1
        elif report.get("baseline", {}).get("solve_rate") is None:
            print("Error: --require-harness: baseline solve_rate is null (harness report missing or invalid)", file=sys.stderr)
            exit_code = 1
        elif report.get("pf", {}).get("solve_rate") is None:
            print("Error: --require-harness: PF solve_rate is null (harness report missing or invalid)", file=sys.stderr)
            exit_code = 1
        else:
            # Predictions and run_status live in the parent of the run dir (e.g. runs/.../baseline/),
            # not necessarily under exp_dir (which may point to experiments/).
            baseline_pred_dir = baseline_run.parent if baseline_run else exp_dir / "baseline"
            pf_pred_dir = pf_run.parent if pf_run else exp_dir / "pf"
            for label, pred_dir, eval_dir, run_dir, report_path in [
                ("baseline", baseline_pred_dir, baseline_eval, baseline_run, br_path),
                ("pf", pf_pred_dir, pf_eval, pf_run, pr_path),
            ]:
                pred_file = pred_dir / "predictions.jsonl"
                if pred_file.exists() and report_path and report_path.exists():
                    pred_mtime = pred_file.stat().st_mtime
                    eval_mtime = report_path.stat().st_mtime
                    # Allow tolerance for clock skew / WSL-Windows mtime; only fail if predictions clearly newer
                    stale_tolerance_s = 60.0
                    if pred_mtime > eval_mtime + stale_tolerance_s:
                        print(
                            "Error: --require-harness: predictions file is newer than eval report (%s); re-run harness before compare"
                            % label,
                            file=sys.stderr,
                        )
                        exit_code = 1
                        break
                status_path = pred_dir / "run_status.json"
                if not status_path.exists():
                    print("Error: --require-harness: run_status.json not found in %s (run_id check skipped)" % pred_dir, file=sys.stderr)
                    exit_code = 1
                    break
                try:
                    run_status = json.loads(status_path.read_text(encoding="utf-8"))
                except (json.JSONDecodeError, OSError) as e:
                    print("Error: --require-harness: failed to read run_status.json in %s: %s" % (pred_dir, e), file=sys.stderr)
                    exit_code = 1
                    break
                expected_run_id = run_status.get("run_id")
                if not expected_run_id:
                    print("Error: --require-harness: run_id missing in %s" % status_path, file=sys.stderr)
                    exit_code = 1
                    break
                expected_run_id = str(expected_run_id)
                if run_dir and run_dir.exists() and run_dir.name != expected_run_id:
                    print(
                        "Error: --require-harness: run_id mismatch (%s): run_dir.name=%s, run_status.run_id=%s"
                        % (label, run_dir.name, expected_run_id),
                        file=sys.stderr,
                    )
                    exit_code = 1
                    break
                eval_meta_path = eval_dir / "eval_metadata.json"
                if eval_meta_path.exists():
                    try:
                        eval_meta = json.loads(eval_meta_path.read_text(encoding="utf-8"))
                        eval_run_id = eval_meta.get("run_id")
                        if eval_run_id is not None and str(eval_run_id) != expected_run_id:
                            print(
                                "Error: --require-harness: run_id mismatch (%s): eval_metadata.run_id=%s, run_status.run_id=%s"
                                % (label, eval_run_id, expected_run_id),
                                file=sys.stderr,
                            )
                            exit_code = 1
                            break
                    except (json.JSONDecodeError, OSError):
                        pass
                pred_sha_path = pred_dir / "predictions.sha256"
                if eval_meta_path.exists() and pred_sha_path.exists():
                    try:
                        eval_meta = json.loads(eval_meta_path.read_text(encoding="utf-8"))
                        stored_sha = eval_meta.get("predictions_sha256")
                        current_sha = pred_sha_path.read_text(encoding="utf-8").strip()
                        if stored_sha and current_sha and stored_sha != current_sha:
                            print(
                                "Error: --require-harness: predictions_sha256 mismatch (%s): eval was run on different predictions"
                                % label,
                                file=sys.stderr,
                            )
                            exit_code = 1
                            break
                    except (json.JSONDecodeError, OSError):
                        pass

            # Budget drift: baseline and PF must use same timeout_sec, max_steps, max_tool_calls, model_params
            if exit_code == 0 and baseline_run and baseline_run.exists() and pf_run and pf_run.exists():
                base_man = _load_run_manifest(baseline_run)
                pf_man = _load_run_manifest(pf_run)
                if base_man is not None and pf_man is not None:
                    base_budget = _budget_slice(base_man)
                    pf_budget = _budget_slice(pf_man)
                    drift: dict[str, Any] = {}
                    for key in list(base_budget) + list(pf_budget):
                        if base_budget.get(key) != pf_budget.get(key):
                            drift[key] = {"baseline": base_budget.get(key), "pf": pf_budget.get(key)}
                    if drift:
                        report["budget_drift"] = drift
                        print(
                            "Error: --require-harness: baseline and PF run configs differ (budget_drift). "
                            "Ensure same timeout_sec, max_steps, max_tool_calls, model, model_params for parity.",
                            file=sys.stderr,
                        )
                        for k, v in drift.items():
                            print("  %s: baseline=%s pf=%s" % (k, v.get("baseline"), v.get("pf")), file=sys.stderr)
                        exit_code = 1

    if args.require_compliance:
        if not pf_run or not pf_run.exists():
            print("Error: --require-compliance: PF run dir not set or does not exist", file=sys.stderr)
            exit_code = 1
        else:
            missing = []
            for d in pf_run.iterdir():
                if not d.is_dir() or d.name.startswith("."):
                    continue
                if (d / "metadata.json").exists() and not (d / COMPLIANCE_FILENAME).exists():
                    missing.append(d.name)
            if missing:
                print(
                    "Error: --require-compliance: missing policy_compliance_summary.json for %d instance(s), e.g. %s"
                    % (len(missing), missing[:3]),
                    file=sys.stderr,
                )
                exit_code = 1

    if args.require_patch_apply:
        pa = report.get("patch_apply") or {}
        applies_false = pa.get("applies_false") or 0
        if applies_false != 0:
            print(
                "Error: --require-patch-apply: patch_apply.applies_false=%s (must be 0 for Step 2 parity; fix patch extraction or apply logic before interpreting solve rates)"
                % applies_false,
                file=sys.stderr,
            )
            print(
                "Hint: compare.json is still written for diagnosis. Non-strict gate: "
                "PF_AB_GATE_ALLOW_EXPLORE=1 and run_direct_agent_ab_gate.py --explore-compare "
                "(see bench/swebench/README.md).",
                file=sys.stderr,
            )
            exit_code = 1

    pa_total = (report.get("patch_apply") or {}).get("total") or 0
    if (
        pa_total == 0
        and baseline_run
        and baseline_run.exists()
        and pf_run
        and pf_run.exists()
    ):
        print(
            "Warning: patch_apply.total is 0 but both run dirs were provided; "
            "ensure summary.json exists in each run dir with an instances list.",
            file=sys.stderr,
        )

    if args.require_priced_models:
        from experiments.scripts.model_pricing import pricing_errors_for_block

        _pe = pricing_errors_for_block(report.get("estimated_cost_usd"))
        for err in _pe:
            print("Error: --require-priced-models: %s" % err, file=sys.stderr)
        if _pe:
            exit_code = 1

    compare_json = out_dir / "compare.json"
    compare_csv = out_dir / "compare.csv"

    with open(compare_json, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    schema_path = _REPO_ROOT / "experiments" / "schemas" / "compare_report.schema.json"
    if schema_path.exists():
        try:
            import jsonschema
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            jsonschema.validate(report, schema)
        except ImportError:
            print("jsonschema not installed; skipping compare.json schema validation", file=sys.stderr)
        except jsonschema.ValidationError as e:
            print("Error: compare.json failed schema validation: %s" % (e.message if hasattr(e, "message") else e), file=sys.stderr)
            exit_code = 1

    rows = build_csv_rows(baseline_eval, pf_eval, baseline_run, pf_run, report)
    if rows:
        fieldnames = ["instance_id"]
        seen = {"instance_id"}
        for r in rows:
            for k in r:
                if k not in seen:
                    fieldnames.append(k)
                    seen.add(k)
        with open(compare_csv, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)

    metrics_full_path = out_dir / "metrics_full.json"
    exp_id = exp_dir.name if exp_dir.name else "unknown"
    with open(metrics_full_path, "w", encoding="utf-8") as f:
        json.dump(build_metrics_full(report, exp_id), f, indent=2)

    print(f"Wrote {compare_json}")
    print(f"Wrote {compare_csv}")
    print(f"Wrote {metrics_full_path}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
