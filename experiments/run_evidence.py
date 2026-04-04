# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Shared helpers for reading PF run evidence (summary, cost_report, compliance, replay bundle).
# Used by compare_runs, categorize_pf_failures, and validate_pf_run.

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

# Re-export from single source of truth (bench.swebench.constants)
from bench.swebench.constants import (
    COMPLIANCE_FILENAME,
    COST_REPORT_FILENAME,
    PATCH_APPLY_CHECK_FILENAME,
    PROOF_OK_FILENAME,
    REPLAY_BUNDLE_FILENAME,
    SUMMARY_JSON_FILENAME,
    TIMING_JSON_FILENAME,
)

__all__ = [
    "COMPLIANCE_FILENAME",
    "COST_REPORT_FILENAME",
    "PATCH_APPLY_CHECK_FILENAME",
    "PROOF_OK_FILENAME",
    "REPLAY_BUNDLE_FILENAME",
    "SUMMARY_JSON_FILENAME",
    "TIMING_JSON_FILENAME",
    "load_summary",
    "load_cost_report",
    "load_compliance",
    "load_patch_apply_check",
    "load_timing",
    "has_replay_bundle",
    "has_proof_ok",
]


def load_timing(run_dir: Path, instance_id: str) -> dict[str, Any] | None:
    """Load runs/<run_id>/<sanitized_id>/timing.json if present (wall_clock_s, tool_calls, timeout_reached, termination_reason)."""
    sanitize = _get_sanitize()
    p = Path(run_dir) / sanitize(instance_id) / TIMING_JSON_FILENAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def _get_sanitize():
    # Lazy import so this module can be imported without repo root when only constants are needed
    from bench.swebench.util import sanitize_instance_id
    return sanitize_instance_id


def load_summary(run_dir: Path) -> dict[str, Any] | None:
    """Load runs/<run_id>/summary.json if present."""
    p = Path(run_dir) / SUMMARY_JSON_FILENAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def load_cost_report(run_dir: Path, instance_id: str) -> dict[str, Any] | None:
    """Load runs/<run_id>/<sanitized_id>/cost_report.json if present."""
    sanitize = _get_sanitize()
    p = Path(run_dir) / sanitize(instance_id) / COST_REPORT_FILENAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def load_compliance(run_dir: Path, instance_id: str) -> dict[str, Any] | None:
    """Load runs/<run_id>/<sanitized_id>/policy_compliance_summary.json if present."""
    sanitize = _get_sanitize()
    p = Path(run_dir) / sanitize(instance_id) / COMPLIANCE_FILENAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def load_patch_apply_check(run_dir: Path, instance_id: str) -> dict[str, Any] | None:
    """Load runs/<run_id>/<sanitized_id>/patch_apply_check.json if present."""
    sanitize = _get_sanitize()
    p = Path(run_dir) / sanitize(instance_id) / PATCH_APPLY_CHECK_FILENAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def has_replay_bundle(run_dir: Path, instance_id: str) -> bool:
    """Return True if runs/<run_id>/<sanitized_id>/replay_bundle.json exists."""
    sanitize = _get_sanitize()
    return (Path(run_dir) / sanitize(instance_id) / REPLAY_BUNDLE_FILENAME).exists()


def has_proof_ok(run_dir: Path) -> bool:
    """Return True if runs/<run_id>/proof.ok exists."""
    return (Path(run_dir) / PROOF_OK_FILENAME).exists()
