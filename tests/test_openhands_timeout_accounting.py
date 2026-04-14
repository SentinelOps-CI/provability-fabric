# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations


def test_timeout_budget_phases_sum_to_total() -> None:
    from bench.swebench.engines.openhands_engine import _compute_timeout_budget_phases

    startup, action, finalization = _compute_timeout_budget_phases(100)
    assert startup is not None
    assert action is not None
    assert finalization is not None
    assert round(startup + action + finalization, 3) == 100.0


def test_latency_extraction_first_action_and_first_file_edit() -> None:
    from bench.swebench.engines.openhands_engine import _extract_latency_metrics_from_events

    raw_events = [
        {"timestamp": "2026-01-01T00:00:00Z", "kind": "MessageEvent"},
        {"timestamp": "2026-01-01T00:00:05Z", "kind": "ActionEvent", "tool_name": "run_terminal_cmd"},
        {"timestamp": "2026-01-01T00:00:07Z", "kind": "ActionEvent", "tool_name": "edit_file"},
    ]
    first_action_latency_s, first_file_edit_latency_s = _extract_latency_metrics_from_events(raw_events)
    assert first_action_latency_s == 5.0
    assert first_file_edit_latency_s == 7.0

