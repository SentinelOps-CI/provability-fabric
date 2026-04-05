#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Shared gate checks for compare.json (used by verify_publish_bundle and callers).
# Returns a list of error messages; empty list means all gates pass.

from __future__ import annotations


def check_compare_gates(compare: dict) -> list[str]:
    """
    Validate compare report against release-checklist gates.
    Returns list of error messages (empty if all pass).
    """
    errors: list[str] = []
    baseline = compare.get("baseline") or {}
    pf = compare.get("pf") or {}
    bl_rate = baseline.get("solve_rate")
    pf_rate = pf.get("solve_rate")
    if bl_rate is not None and not isinstance(bl_rate, (int, float)):
        errors.append("baseline.solve_rate must be a number or null")
    if pf_rate is not None and not isinstance(pf_rate, (int, float)):
        errors.append("pf.solve_rate must be a number or null")
    patch_apply = compare.get("patch_apply") or {}
    applies_false = patch_apply.get("applies_false", -1)
    if applies_false != 0:
        errors.append("patch_apply.applies_false must be 0 (got %s)" % applies_false)
    replay = compare.get("replay") or {}
    if "success_rate" not in replay:
        errors.append("compare.json must have replay.success_rate (replay section)")
    policy = compare.get("policy")
    if policy is None or not isinstance(policy, dict):
        errors.append("compare.json must have a non-empty policy section")
    return errors
