# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Cost report aggregation invariants (stdlib property-style checks).

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.cost_reporter import CostReporter


def test_aggregate_monotonic_adding_report_increases_or_equal_totals():
    base = [{"instance_id": "a", "prompt_tokens": 10, "completion_tokens": 5}]
    t0 = CostReporter.aggregate_token_totals(base)
    extended = base + [{"instance_id": "b", "prompt_tokens": 3, "completion_tokens": 7}]
    t1 = CostReporter.aggregate_token_totals(extended)
    assert t1["prompt_tokens_total"] >= t0["prompt_tokens_total"]
    assert t1["completion_tokens_total"] >= t0["completion_tokens_total"]


def test_aggregate_single_report_matches_fields():
    r = [{"instance_id": "x", "prompt_tokens": 42, "completion_tokens": 7}]
    t = CostReporter.aggregate_token_totals(r)
    assert t["prompt_tokens_total"] == 42
    assert t["completion_tokens_total"] == 7
