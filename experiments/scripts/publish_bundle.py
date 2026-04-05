#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Single definition of "valid publish bundle": required files, required dirs, GOLDEN.ok keys.
# Used by verify_publish_bundle.py and export_publish_artifacts.py so both stay in sync.

from __future__ import annotations

# Files that must exist in the publish root (verifier checks; export produces all except GOLDEN.ok).
# MANIFEST.sha256 is written after GOLDEN.ok/RESULTS.md/VERIFY.md by update_run_ids_if_green.
PUBLISH_BUNDLE_REQUIRED_FILES = (
    "GOLDEN.ok",
    "all_preds.jsonl",
    "metadata.yaml",
    "MANIFEST.sha256",
    "metrics_full.json",
)

# Directories that must exist; each must contain at least one instance (logs/<id>/, trajs/<id>.json).
PUBLISH_BUNDLE_REQUIRED_DIRS = ("logs", "trajs")

# GOLDEN.ok JSON must contain these keys (machine-readable stamp from update_run_ids_if_green).
GOLDEN_OK_REQUIRED_KEYS = (
    "baseline_run_id",
    "pf_run_id",
    "pf_commit",
    "timestamp_utc",
    "parity_gate_passed",
)

# Files/dirs that export_publish_artifacts.py produces (subset of required; GOLDEN.ok added by update_run_ids).
EXPORT_PRODUCES_FILES = ("all_preds.jsonl", "metadata.yaml")
EXPORT_PRODUCES_DIRS = ("logs", "trajs")
