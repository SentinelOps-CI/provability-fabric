#!/usr/bin/env bash
# PF-Guarded Runtime executor. Set as SHELL when running OpenHands with --guarded.
# Requires: PF_GUARD_WORKSPACE, PF_GUARD_LEDGER_DIR or PF_GUARD_EVENTS_PATH, PF_GUARD_RUN_ID.
# Optional: PF_REPO_ROOT (repo root for python -m).
set -e
REPO_ROOT="${PF_REPO_ROOT:-.}"
cd "$REPO_ROOT"
exec python3 -m bench.swebench.guard.executor "$@"
