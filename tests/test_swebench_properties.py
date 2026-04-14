# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Deterministic invariant checks (no Hypothesis dependency).

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.cost_reporter import CostReporter
from bench.swebench.workspace import WorkspaceManifest


def test_aggregate_token_totals_idempotent_empty():
    assert CostReporter.aggregate_token_totals([]) == {
        "prompt_tokens_total": 0,
        "completion_tokens_total": 0,
    }


def test_workspace_manifest_sha256_stable():
    m1 = WorkspaceManifest(
        instance_id="i",
        repo="o/r",
        base_commit="abc",
        workspace_root="/w",
        repo_path="/w/r",
        task_prompt_path="/w/t",
        scratch_path="/w/s",
        resolved_commit="def",
    )
    h1 = m1.sha256()
    h2 = m1.sha256()
    assert h1 == h2
    assert len(h1) == 64


def test_cost_aggregate_token_totals_associative():
    """Splitting the report list should not change the summed tokens."""
    reports = [
        {"instance_id": "a", "prompt_tokens": 1, "completion_tokens": 2},
        {"instance_id": "b", "prompt_tokens": 3, "completion_tokens": 4},
        {"instance_id": "c", "prompt_tokens": 5, "completion_tokens": 6},
    ]
    full = CostReporter.aggregate_token_totals(reports)
    mid = CostReporter.aggregate_token_totals(reports[:2])
    last = CostReporter.aggregate_token_totals(reports[2:])
    assert (
        full["prompt_tokens_total"]
        == mid["prompt_tokens_total"] + last["prompt_tokens_total"]
    )
    assert (
        full["completion_tokens_total"]
        == mid["completion_tokens_total"] + last["completion_tokens_total"]
    )
