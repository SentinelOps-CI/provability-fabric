#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Create or reuse a dedicated venv for SWE-bench + OpenHands and install deps.
# Avoids conflicts with other projects (corridor-os, crewai, guardrails-ai, etc.).
# Run from repository root **in WSL or Linux** (real runs and harness require Unix).
set -e

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

VENV_DIR="${VENV_DIR:-$REPO_ROOT/.venv-wsl}"
echo "=== SWE-bench + OpenHands venv ==="
echo "Venv path: $VENV_DIR"

_py_ge_312() {
  "$1" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 12) else 1)' 2>/dev/null
}

_create_venv_with_uv() {
  if ! command -v uv >/dev/null 2>&1; then
    echo "ERROR: python3 is older than 3.12 and uv is not on PATH."
    echo "OpenHands (PyPI) needs Python >= 3.12. On Debian 12 bookworm, apt often has no python3.12."
    echo "Install uv, reload your shell, then re-run this script:"
    echo "  curl -LsSf https://astral.sh/uv/install.sh | sh"
    echo "  exec \"\$SHELL\" -l"
    exit 1
  fi
  echo "Installing CPython 3.12 via uv and creating venv..."
  uv python install 3.12
  # uv venv omits pip by default; without --seed, `python -m pip` fails and the shell may fall
  # back to Debian's PEP 668 "externally managed" pip (misleading error).
  uv venv --python 3.12 --seed "$VENV_DIR"
}

if [ -x "$VENV_DIR/bin/python" ]; then
  if ! _py_ge_312 "$VENV_DIR/bin/python"; then
    echo "Existing venv is not Python 3.12+ (OpenHands PyPI requires >= 3.12)."
    if command -v uv >/dev/null 2>&1; then
      echo "Removing $VENV_DIR and recreating with uv (Python 3.12)..."
      rm -rf "$VENV_DIR"
      _create_venv_with_uv
    else
      echo "Remove the venv or set VENV_DIR to a new path, then install uv and re-run:"
      echo "  rm -rf \"$VENV_DIR\""
      echo "  curl -LsSf https://astral.sh/uv/install.sh | sh"
      exit 1
    fi
  fi
else
  echo "Creating venv..."
  if _py_ge_312 python3; then
    python3 -m venv "$VENV_DIR"
  else
    _create_venv_with_uv
  fi
fi

echo "Activating venv..."
# shellcheck source=/dev/null
. "$VENV_DIR/bin/activate"

REQ_FILE="$REPO_ROOT/bench/swebench/requirements-swebench.txt"
if python -m pip --version >/dev/null 2>&1; then
  echo "Upgrading pip..."
  python -m pip install --upgrade pip -q
  echo "Installing from bench/swebench/requirements-swebench.txt (datasets, swebench, openhands)..."
  pip install -r "$REQ_FILE"
else
  if ! command -v uv >/dev/null 2>&1; then
    echo "ERROR: This venv has no pip (typical for uv venv without --seed) and uv is not on PATH."
    echo "Recreate with: uv venv --python 3.12 --seed \"$VENV_DIR\""
    echo "Or install deps with: uv pip install --python \"$VENV_DIR/bin/python\" -r \"$REQ_FILE\""
    exit 1
  fi
  echo "No pip in venv; installing requirements with uv pip..."
  uv pip install --python "$VENV_DIR/bin/python" -r "$REQ_FILE"
fi

echo ""
echo "Verifying Python packages..."
python -c "import datasets, swebench, openhands; print('datasets, swebench, openhands: ok')"

CHECK_SCRIPT="$REPO_ROOT/experiments/scripts/check_wsl_env.py"
if [ -f "$CHECK_SCRIPT" ]; then
  echo ""
  echo "Running full preflight (Docker + modules)..."
  if ! python "$CHECK_SCRIPT"; then
    echo ""
    echo "Warning: check_wsl_env.py failed (often Docker not installed or daemon not running)." >&2
    echo "  Install/start Docker, then: source $VENV_DIR/bin/activate && python experiments/scripts/check_wsl_env.py" >&2
  fi
else
  echo ""
  echo "Note: missing $CHECK_SCRIPT (pull latest feat/swebench-gate-vm-bundle for the full preflight script)."
fi

echo ""
echo "Done. Activate this venv before running the runner:"
echo "  source $VENV_DIR/bin/activate"
echo "Then run baseline/PF from repo root: bash experiments/scripts/run-baseline-pf-cycle.sh"
echo ""
echo "Disk (GCP / small VMs): a 10 GB boot disk is usually too small for Docker + HF/datasets cache"
echo "  + workspace clones. Run df -h before long jobs; if space is tight, resize the disk, set"
echo "  HF_HOME on a larger volume, prune docker images, and remove stale workspaces/. Details:"
echo "  bench/swebench/README.md (Disk space)."
echo ""
echo "Long SSH sessions: install tmux/screen once (avoids losing the gate on disconnect):"
echo "  bash experiments/scripts/install_vm_runner_extras.sh"
