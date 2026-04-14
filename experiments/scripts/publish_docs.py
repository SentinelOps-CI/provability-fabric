#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Build PUBLISH.md, RESULTS.md, and VERIFY.md content for the publish bundle.
# Single source of truth for reviewer-facing docs (testable, no I/O).

from __future__ import annotations

from pathlib import Path
from typing import Any


def _na(v: Any) -> str:
    return "N/A" if v is None else str(v)


def build_publish_md(
    baseline_run_id: str,
    pf_run_id: str,
    compare_data: dict[str, Any],
) -> list[str]:
    """Build PUBLISH.md lines (summary table + env drift)."""
    b = compare_data.get("baseline") or {}
    p = compare_data.get("pf") or {}
    r = compare_data.get("replay") or {}
    env_drift = compare_data.get("env_drift")
    return [
        "# Publish summary (green run)",
        "",
        "| Field | Value |",
        "|-------|-------|",
        "| Baseline run_id | %s |" % baseline_run_id,
        "| PF run_id | %s |" % pf_run_id,
        "| Baseline solve_rate | %s |" % _na(b.get("solve_rate")),
        "| PF solve_rate | %s |" % _na(p.get("solve_rate")),
        "| PF policy_violation_rate_final | %s |" % _na(p.get("policy_violation_rate_final")),
        "| Replay success_rate | %s |" % _na(r.get("success_rate")),
        "",
        "## Env drift",
        "Present: %s" % ("yes" if env_drift else "no (or empty)"),
    ]


def build_results_md(
    baseline_run_id: str,
    pf_run_id: str,
    git_sha: str,
    timestamp_utc: str,
    compare_data: dict[str, Any],
    parity_gate_passed: bool | None,
) -> list[str]:
    """Build RESULTS.md lines (audit-friendly: run IDs, solve rates, patch_apply, violations, replay, layout)."""
    b = compare_data.get("baseline") or {}
    p = compare_data.get("pf") or {}
    r = compare_data.get("replay") or {}
    pa = compare_data.get("patch_apply") or {}
    policy = compare_data.get("policy") or {}
    env_drift = compare_data.get("env_drift")
    delta = compare_data.get("delta") or {}
    lines = [
        "# Results (green run)",
        "",
        "How to audit this run.",
        "",
        "## Run identifiers",
        "| Field | Value |",
        "|-------|-------|",
        "| Baseline run_id | %s |" % baseline_run_id,
        "| PF run_id | %s |" % pf_run_id,
        "| PF commit | %s |" % (git_sha or "unknown"),
        "| Timestamp (UTC) | %s |" % timestamp_utc,
        "",
        "## Solve rates and delta",
        "| Metric | Value |",
        "|--------|-------|",
        "| Baseline solve_rate | %s |" % _na(b.get("solve_rate")),
        "| PF solve_rate | %s |" % _na(p.get("solve_rate")),
        "| Delta (pf - baseline) | %s |" % _na(delta.get("solve_rate")),
        "| Parity gate (pf >= baseline - 0.01) | %s |" % _na(parity_gate_passed),
        "",
        "## Per-attempt cost and latency (compare.json)",
        "Useful when solve_rate is 0: **cost_per_attempt** and **latency_per_attempt** still aggregate over all instances.",
        "",
        "| Metric | Baseline | PF |",
        "|--------|----------|-----|",
    ]
    bcpa = b.get("cost_per_attempt") or {}
    pcpa = p.get("cost_per_attempt") or {}
    lines.extend([
        "| Avg wall_clock_s (attempt) | %s | %s |"
        % (_na(bcpa.get("wall_clock_s")), _na(pcpa.get("wall_clock_s"))),
        "| Avg total tokens / attempt | %s | %s |"
        % (
            _na(
                (bcpa.get("prompt_tokens") or 0) + (bcpa.get("completion_tokens") or 0)
                if bcpa.get("n")
                else None
            ),
            _na(
                (pcpa.get("prompt_tokens") or 0) + (pcpa.get("completion_tokens") or 0)
                if pcpa.get("n")
                else None
            ),
        ),
    ])
    bla = b.get("latency_per_attempt") or {}
    pla = p.get("latency_per_attempt") or {}
    lines.extend([
        "| Wall clock median (s) | %s | %s |" % (_na(bla.get("median")), _na(pla.get("median"))),
        "| Wall clock p95 (s) | %s | %s |" % (_na(bla.get("p95")), _na(pla.get("p95"))),
    ])
    ec = compare_data.get("estimated_cost_usd") or {}
    eb = (ec.get("baseline") or {}) if isinstance(ec, dict) else {}
    ep = (ec.get("pf") or {}) if isinstance(ec, dict) else {}
    lines.extend([
        "| Est. total USD (indicative) | %s | %s |" % (_na(eb.get("total_usd")), _na(ep.get("total_usd"))),
        "| Pricing table version | %s |" % _na(ec.get("pricing_version") if isinstance(ec, dict) else None),
        "",
        "## Harness test runtime (compare.json harness_eval)",
        "Per-instance seconds from SWE-bench **run_instance.log** (test phase in container; not agent time). See also **metrics_full.json**.",
        "",
        "| Metric | Baseline | PF |",
        "|--------|----------|-----|",
    ])
    he = compare_data.get("harness_eval") or {}
    hb = (he.get("baseline") or {}) if isinstance(he, dict) else {}
    hp = (he.get("pf") or {}) if isinstance(he, dict) else {}
    sb = hb.get("summary") or {}
    sp = hp.get("summary") or {}
    lines.extend([
        "| Parsed instances (n) | %s | %s |" % (_na(hb.get("n_parsed")), _na(hp.get("n_parsed"))),
        "| Test runtime median (s) | %s | %s |" % (_na(sb.get("median")), _na(sp.get("median"))),
        "| Test runtime p95 (s) | %s | %s |" % (_na(sb.get("p95")), _na(sp.get("p95"))),
        "",
        "## Patch apply",
    ])
    lines.extend([
        "| Field | Value |",
        "|-------|-------|",
        "| total | %s |" % _na(pa.get("total")),
        "| applies_true | %s |" % _na(pa.get("applies_true")),
        "| applies_false | %s |" % _na(pa.get("applies_false")),
        "",
        "## Violations summary (PF)",
        "| Metric | Value |",
        "|--------|-------|",
        "| policy_violation_rate_final | %s |" % _na(p.get("policy_violation_rate_final")),
        "",
        "Top reason codes (policy):",
    ])
    for item in (policy.get("reason_codes_topN") or [])[:10]:
        lines.append("- %s: %s" % (item.get("reason_code", ""), item.get("count", 0)))
    lines.extend([
        "",
        "## Replay summary",
        "| Field | Value |",
        "|-------|-------|",
        "| sample_size | %s |" % _na(r.get("sample_size")),
        "| success_rate | %s |" % _na(r.get("success_rate")),
        "| mismatch_count | %s |" % _na(r.get("mismatch_count")),
        "",
        "## Env drift",
        "Present: %s" % ("yes" if env_drift else "no (or empty)"),
        "",
        "## Artifact layout",
        "- Predictions: all_preds.jsonl",
        "- Run card: metrics_full.json (solve rates, harness_eval summary, cost estimate)",
        "- Logs per instance: logs/<instance_id>/",
        "- Trajectories: trajs/<instance_id>.json",
        "- Metadata: metadata.yaml",
    ])
    return lines


def build_verify_md(
    exp_dir_name: str,
    publish_dir: Path | str,
    compare_json_path: Path | str,
) -> list[str]:
    """Build VERIFY.md lines (factual entrypoint for external audit; links only to artifacts)."""
    publish_dir = Path(publish_dir)
    compare_json_path = Path(compare_json_path)
    return [
        "# Verify this bundle",
        "",
        "Factual entrypoint for external audit. Links only to generated artifacts.",
        "",
        "## What command produced this bundle?",
        "```bash",
        "bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids",
        "```",
        "From repository root on WSL/Linux. run-ids.md is updated only when all gates pass.",
        "",
        "## Where are the run IDs and commits pinned?",
        "- **GOLDEN.ok** (this directory): baseline_run_id, pf_run_id, pf_commit, timestamp_utc, parity_gate_passed.",
        "- **run-ids.md**: `experiments/%s/run-ids.md` (updated only by update_run_ids_if_green.py)." % exp_dir_name,
        "",
        "## Where are the harness reports?",
        "- Baseline eval: `runs/%s/baseline/eval/` (harness report + eval_metadata.json)." % exp_dir_name,
        "- PF eval: `runs/%s/pf/eval/` (harness report + eval_metadata.json)." % exp_dir_name,
        "",
        "## Where is replay evidence?",
        "- **replay_summary.json**: `runs/%s/replay_summary.json` (sample_size, success_rate, mismatch_count, replay_fail_reasons_topN)." % exp_dir_name,
        "- **replay/instance_results.jsonl**: `runs/%s/replay/instance_results.jsonl` (per-instance patch hashes, match, failure_reason)." % exp_dir_name,
        "",
        "## What are the acceptance gates and did they pass?",
        "- baseline.solve_rate and pf.solve_rate numeric: see compare.json (or RESULTS.md).",
        "- patch_apply.applies_false == 0: see compare.json.",
        "- budget_drift absent or empty: see compare.json.",
        "- policy section non-empty: see compare.json.",
        "- replay section present: see compare.json.",
        "- Publish bundle: all_preds.jsonl, metrics_full.json, logs/<instance_id>/, trajs/<instance_id>.json, GOLDEN.ok (this directory).",
        "",
        "To run the machine verifier (no network, no Docker):",
        "```bash",
        "python experiments/scripts/verify_publish_bundle.py --publish-dir %s --compare-json %s" % (publish_dir, compare_json_path),
        "```",
    ]
