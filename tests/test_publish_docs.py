# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Unit tests for publish_docs: build_verify_md, build_results_md, build_publish_md.
# Pure functions with minimal mock compare_data; assert key sections appear. No I/O.

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from experiments.scripts.publish_docs import (
    build_verify_md,
    build_results_md,
    build_publish_md,
)


def test_build_publish_md_run_ids_and_solve_rate_and_env_drift():
    """build_publish_md output contains baseline_run_id, pf_run_id, solve_rate, env_drift."""
    compare_data = {
        "baseline": {"solve_rate": 0.4},
        "pf": {"solve_rate": 0.35, "policy_violation_rate_final": 0.02},
        "replay": {"success_rate": 0.9},
        "env_drift": {"pip_freeze_hash": "abc"},
    }
    lines = build_publish_md(
        baseline_run_id="base-123",
        pf_run_id="pf-456",
        compare_data=compare_data,
    )
    text = "\n".join(lines)
    assert "base-123" in text
    assert "pf-456" in text
    assert "0.4" in text
    assert "0.35" in text
    assert "Env drift" in text
    assert "yes" in text  # env_drift present


def test_build_publish_md_env_drift_absent():
    """build_publish_md shows env_drift absent when not in compare_data."""
    compare_data = {"baseline": {"solve_rate": 0.5}, "pf": {"solve_rate": 0.5}}
    lines = build_publish_md(
        baseline_run_id="b",
        pf_run_id="p",
        compare_data=compare_data,
    )
    text = "\n".join(lines)
    assert "Env drift" in text
    assert "no (or empty)" in text


def test_build_results_md_run_ids_solve_rate_parity_gate_env_drift():
    """build_results_md output contains run IDs, solve_rate, parity_gate_passed, env_drift."""
    compare_data = {
        "baseline": {"solve_rate": 0.5},
        "pf": {"solve_rate": 0.48, "policy_violation_rate_final": 0.0},
        "replay": {"sample_size": 20, "success_rate": 1.0, "mismatch_count": 0},
        "patch_apply": {"total": 10, "applies_true": 10, "applies_false": 0},
        "policy": {"reason_codes_topN": [{"reason_code": "ok", "count": 10}]},
        "env_drift": None,
        "delta": {"solve_rate": -0.02},
    }
    lines = build_results_md(
        baseline_run_id="base-1",
        pf_run_id="pf-1",
        git_sha="abc123",
        timestamp_utc="2025-01-15T12:00:00Z",
        compare_data=compare_data,
        parity_gate_passed=True,
    )
    text = "\n".join(lines)
    assert "base-1" in text
    assert "pf-1" in text
    assert "0.5" in text
    assert "0.48" in text
    assert "True" in text or "true" in text  # parity_gate_passed
    assert "Env drift" in text
    assert "no (or empty)" in text
    assert "Results (green run)" in text
    assert "Per-attempt cost and latency" in text


def test_build_results_md_per_attempt_and_estimated_usd():
    compare_data = {
        "baseline": {
            "solve_rate": 0.0,
            "cost_per_attempt": {
                "prompt_tokens": 100,
                "completion_tokens": 50,
                "wall_clock_s": 120.5,
                "n": 5,
            },
            "latency_per_attempt": {"median": 100.0, "p95": 200.0},
        },
        "pf": {
            "solve_rate": 0.0,
            "cost_per_attempt": {
                "prompt_tokens": 110,
                "completion_tokens": 55,
                "wall_clock_s": 135.0,
                "n": 5,
            },
            "latency_per_attempt": {"median": 110.0, "p95": 220.0},
        },
        "estimated_cost_usd": {
            "pricing_version": "2026-02-12",
            "baseline": {"total_usd": 0.01},
            "pf": {"total_usd": 0.012},
        },
        "replay": {},
        "patch_apply": {},
        "policy": {},
        "delta": {"solve_rate": 0.0},
    }
    lines = build_results_md("b", "p", "sha", "t", compare_data, True)
    text = "\n".join(lines)
    assert "120.5" in text
    assert "135.0" in text
    assert "0.01" in text
    assert "Per-attempt cost and latency" in text


def test_build_results_md_parity_gate_false():
    """build_results_md includes parity_gate_passed False."""
    compare_data = {
        "baseline": {"solve_rate": 0.5},
        "pf": {"solve_rate": 0.3},
        "replay": {},
        "patch_apply": {},
        "policy": {},
        "delta": {"solve_rate": -0.2},
    }
    lines = build_results_md(
        baseline_run_id="b",
        pf_run_id="p",
        git_sha="sha",
        timestamp_utc="now",
        compare_data=compare_data,
        parity_gate_passed=False,
    )
    text = "\n".join(lines)
    assert "Parity gate" in text or "parity" in text.lower()
    assert "False" in text or "false" in text


def test_build_verify_md_contains_run_ids_golden_and_verify_command():
    """build_verify_md output contains GOLDEN.ok, run IDs placeholder, and verify command."""
    lines = build_verify_md(
        exp_dir_name="exp-step2-lite-smoke",
        publish_dir=Path("/publish"),
        compare_json_path=Path("/compare.json"),
    )
    text = "\n".join(lines)
    assert "Verify this bundle" in text
    assert "GOLDEN.ok" in text
    assert "baseline_run_id" in text or "run_id" in text
    assert "verify_publish_bundle.py" in text
    assert "publish" in text and "compare" in text  # paths may be normalized per OS
    assert "exp-step2-lite-smoke" in text
    assert "metrics_full.json" in text
