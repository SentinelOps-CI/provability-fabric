# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Single source of truth for PF run evidence filenames (run dir layout).
# Import from here in compare_runs, run_evidence, cost_report, proof_hook, replay.

from __future__ import annotations

import os

# Run-level evidence
SUMMARY_JSON_FILENAME = "summary.json"
PROOF_OK_FILENAME = "proof.ok"

# Per-instance evidence (under run_dir / sanitize_instance_id(instance_id) /)
COST_REPORT_FILENAME = "cost_report.json"
COMPLIANCE_FILENAME = "policy_compliance_summary.json"
PATCH_APPLY_CHECK_FILENAME = "patch_apply_check.json"
REPLAY_BUNDLE_FILENAME = "replay_bundle.json"
TIMING_JSON_FILENAME = "timing.json"

# Patch size cap: SWE-bench patches are typically < 100KB; larger diffs are usually build/cache noise.
# Override via PF_MAX_PATCH_BYTES (integer).
MAX_PATCH_BYTES = int(os.environ.get("PF_MAX_PATCH_BYTES", str(2 * 1024 * 1024)))

# Git diff timeout (seconds) for full-repo diff in the OpenHands engine. Override via PF_GIT_DIFF_TIMEOUT.
GIT_DIFF_TIMEOUT = int(os.environ.get("PF_GIT_DIFF_TIMEOUT", "120"))

# --- Engine diff tuning (openhands_engine); single source of truth, overrides optional ---
# Timeout for git diff HEAD --stat (used to decide full vs path-restricted diff).
DIFF_STAT_TIMEOUT = int(os.environ.get("PF_DIFF_STAT_TIMEOUT", "20"))
# Timeout for git diff --name-only when building path list for path-restricted fallback (e.g. django).
NAME_ONLY_QUICK_TIMEOUT = int(os.environ.get("PF_NAME_ONLY_QUICK_TIMEOUT", "30"))
# When trajectory has no file edits, use this short timeout for name-only check; if empty, skip full diff (saves 7–10s).
NO_EDIT_FAST_CHECK_TIMEOUT = int(os.environ.get("PF_NO_EDIT_FAST_CHECK_TIMEOUT", "5"))
# If --stat shows more than this many files, skip full diff and use path-restricted only.
DIFF_STAT_FILE_THRESHOLD = int(os.environ.get("PF_DIFF_STAT_FILE_THRESHOLD", "200"))
# Timeout for path-restricted diff (fewer files, so shorter timeout).
PATH_DIFF_TIMEOUT = int(os.environ.get("PF_PATH_DIFF_TIMEOUT", "60"))
# When path-restricted diff is still over MAX_PATCH_BYTES, try at most this many paths to stay under cap.
PATH_RESTRICTED_MAX_PATHS_FALLBACK = int(os.environ.get("PF_PATH_RESTRICTED_MAX_PATHS", "50"))

# --- Runner / diagnostic (runner.py) ---
# Timeout for diagnostic git diff --stat when patch was capped for size (write_diff_stat_when_too_large).
DIAGNOSTIC_DIFF_STAT_TIMEOUT = int(os.environ.get("PF_DIAGNOSTIC_DIFF_STAT_TIMEOUT", "30"))
# Timeout for git apply --check in run_patch_apply_check.
GIT_APPLY_CHECK_TIMEOUT = int(os.environ.get("PF_GIT_APPLY_CHECK_TIMEOUT", "30"))
# Max length for git_version string in patch_apply_check.json.
GIT_VERSION_MAX_LEN = 200
# Max stderr length stored in patch_apply_check.json (truncate with "... (truncated)").
PATCH_APPLY_CHECK_STDERR_MAX = 2000
# When writing diagnostic diff stat, show this many head and tail lines.
DIFF_STAT_DISPLAY_HEAD = 80
DIFF_STAT_DISPLAY_TAIL = 200
DIFF_STAT_DISPLAY_LINES_THRESHOLD = 300
# Timeout for pip freeze when writing env.json (run-level).
PIP_FREEZE_TIMEOUT = int(os.environ.get("PF_PIP_FREEZE_TIMEOUT", "30"))

# --- Preflight (runner.py _run_preflight) ---
# Timeout for git diff HEAD --stat during preflight; if exceeded, report diff_risk: high.
PREFLIGHT_DIFF_TIMEOUT = int(os.environ.get("PF_PREFLIGHT_DIFF_TIMEOUT", "5"))
# Timeout for git rev-list --count HEAD during preflight.
PREFLIGHT_REV_LIST_TIMEOUT = int(os.environ.get("PF_PREFLIGHT_REV_LIST_TIMEOUT", "10"))
# If preflight diff shows more than this many files changed, report diff_risk: high.
PREFLIGHT_DIFF_RISK_FILE_THRESHOLD = int(os.environ.get("PF_PREFLIGHT_DIFF_RISK_FILE_THRESHOLD", "200"))

# Prime Intellect OpenAI-compatible inference API (used when OPENHANDS_PROVIDER=prime_intellect and
# PRIME_INTELLECT_BASE_URL / OPENAI_BASE_URL are unset). See https://docs.primeintellect.ai/inference/overview
DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL = "https://api.pinference.ai/api/v1"
