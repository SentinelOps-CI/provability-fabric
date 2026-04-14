#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# GCP Debian/Ubuntu (or any Linux) VM: preflight, ensure SWE-bench venv, then the full
# baseline + PF-guarded + harness + strict-compare pipeline (default agent: direct_agent).
#
# Prerequisites: git clone of this repo, Docker installed and running, LLM keys in .env or env.
#
# Usage (from repository root, inside tmux or screen for long SSH sessions):
#   bash experiments/scripts/run_gcp_vm_swebench_baseline_pf_compare.sh
#   bash experiments/scripts/run_gcp_vm_swebench_baseline_pf_compare.sh --update-run-ids --triage
#
# See experiments/scripts/run-baseline-pf-cycle.sh for phase details and experiments/README.md.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

case "$(uname -s 2>/dev/null)" in
  Linux) ;;
  *)
    echo "Error: this launcher requires Linux or WSL (uname -s must be Linux)." >&2
    exit 1
    ;;
esac

if ! command -v tmux >/dev/null 2>&1 && ! command -v screen >/dev/null 2>&1; then
  echo "Warning: neither tmux nor screen is on PATH. SSH disconnects can kill long runs." >&2
  echo "  Install once: bash experiments/scripts/install_vm_runner_extras.sh" >&2
fi

if ! command -v docker >/dev/null 2>&1; then
  echo "Error: docker CLI not found. Install Docker before SWE-bench harness runs." >&2
  exit 1
fi
if ! docker info >/dev/null 2>&1; then
  echo "Error: docker daemon not reachable (docker info failed). Start Docker or fix permissions." >&2
  exit 1
fi

if [ ! -x "$REPO_ROOT/.venv-wsl/bin/python" ]; then
  echo "=== No .venv-wsl: creating SWE-bench + OpenHands venv (first run) ==="
  bash "$REPO_ROOT/experiments/scripts/setup_swebench_venv.sh"
fi

exec bash "$REPO_ROOT/experiments/scripts/run-baseline-pf-cycle.sh" "$@"
