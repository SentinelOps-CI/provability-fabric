#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Path-aware local install. Prefer this over always running install-full.
# Usage:
#   scripts/install-dev.sh                  # auto-detect from git changes
#   scripts/install-dev.sh --scope=go       # go | node | python | rust | all | auto
#   make install-dev SCOPE=node

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SCOPE="auto"
BASE_REF="${BASE_REF:-}"

usage() {
  cat <<'EOF'
Usage: scripts/install-dev.sh [--scope=auto|go|node|python|rust|all]

  Path-aware developer install (not a full platform bootstrap).
  --scope=auto (default) inspects git changes vs BASE_REF (origin/main, else HEAD~1).
  Multiple scopes may be comma-separated (e.g. go,node).

Environment:
  BASE_REF   Git ref for auto detection (default: origin/main or HEAD~1)
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --scope=*|--lang=*) SCOPE="${1#*=}" ;;
    -h|--help) usage; exit 0 ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
  shift
done

# Normalize aliases from the Wave E4 plan (LANG=) without touching shell locale.
SCOPE="$(echo "$SCOPE" | tr '[:upper:]' '[:lower:]' | tr ' ' ',')"

have_cmd() { command -v "$1" >/dev/null 2>&1; }

detect_scopes() {
  local base="$BASE_REF"
  if [[ -z "$base" ]]; then
    if git rev-parse --verify origin/main >/dev/null 2>&1; then
      base="origin/main"
    elif git rev-parse --verify main >/dev/null 2>&1; then
      base="main"
    else
      base="HEAD~1"
    fi
  fi

  local files=""
  if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    files="$(git diff --name-only "${base}...HEAD" 2>/dev/null || true)"
    if [[ -z "$files" ]]; then
      files="$(git diff --name-only --cached 2>/dev/null || true)"
    fi
    if [[ -z "$files" ]]; then
      files="$(git diff --name-only 2>/dev/null || true)"
    fi
  fi

  if [[ -z "$files" ]]; then
    echo "go"
    return 0
  fi

  local scopes=()
  if echo "$files" | grep -E '\.(go)$|/go\.mod$|/go\.sum$' >/dev/null; then
    scopes+=("go")
  fi
  if echo "$files" | grep -E 'package(-lock)?\.json$|tsconfig|/src/.*\.(ts|tsx|js)$' >/dev/null; then
    scopes+=("node")
  fi
  if echo "$files" | grep -E '\.py$|requirements\.txt$|pytest' >/dev/null; then
    scopes+=("python")
  fi
  if echo "$files" | grep -E 'Cargo\.(toml|lock)$|\.rs$' >/dev/null; then
    scopes+=("rust")
  fi

  if [[ ${#scopes[@]} -eq 0 ]]; then
    echo "go"
  else
    # Deduplicate while preserving order
    printf '%s\n' "${scopes[@]}" | awk '!seen[$0]++' | paste -sd, -
  fi
}

install_go() {
  echo "==> Go: workspace + CLI"
  bash scripts/go-work-init.sh
  if ! have_cmd go; then
    echo "Go not installed; skip CLI build. Install Go 1.23+ from https://go.dev/dl/" >&2
    return 0
  fi
  (cd core/cli/pf && go build -o pf .)
  echo "Built core/cli/pf/pf"
}

install_node() {
  echo "==> Node: scoped package installs"
  if ! have_cmd npm; then
    echo "npm not found; skip Node installs" >&2
    return 0
  fi
  local dirs=(
    runtime/ledger
    core/sdk/typescript
    core/crypto/dsse-ts
  )
  local d
  for d in "${dirs[@]}"; do
    if [[ -f "$d/package.json" ]]; then
      echo "Installing $d ..."
      if [[ -f "$d/package-lock.json" ]]; then
        (cd "$d" && npm ci --no-fund --no-audit)
      else
        (cd "$d" && npm install --no-fund --no-audit)
      fi
      if [[ "$d" == "runtime/ledger" ]] && grep -q '"prisma:generate"' "$d/package.json" 2>/dev/null; then
        (cd "$d" && npm run prisma:generate) || true
      fi
    fi
  done
}

install_python() {
  echo "==> Python: test tooling"
  local py=""
  if have_cmd python3; then py=python3
  elif have_cmd python; then py=python
  else
    echo "Python not found; skip" >&2
    return 0
  fi
  "$py" -m pip install --upgrade pip >/dev/null
  "$py" -m pip install pytest jsonschema pyyaml requests
  for req in tests/integration/requirements.txt tools/cert-validate/requirements.txt; do
    if [[ -f "$req" ]]; then
      "$py" -m pip install -r "$req" || true
    fi
  done
}

install_rust() {
  echo "==> Rust: fetch workspace"
  if ! have_cmd cargo; then
    echo "cargo not found; skip (install from https://rustup.rs/)" >&2
    return 0
  fi
  cargo fetch
}

install_all() {
  echo "==> Full install via scripts/install.sh --full"
  bash scripts/install.sh --full
}

if [[ "$SCOPE" == "auto" ]]; then
  SCOPE="$(detect_scopes)"
  echo "Auto-detected scopes: $SCOPE"
fi

IFS=',' read -r -a SCOPE_LIST <<< "$SCOPE"
for s in "${SCOPE_LIST[@]}"; do
  case "$s" in
    go) install_go ;;
    node) install_node ;;
    python|py) install_python ;;
    rust) install_rust ;;
    all|full)
      install_all
      exit 0
      ;;
    "" ) ;;
    *)
      echo "Unknown scope: $s (expected go|node|python|rust|all|auto)" >&2
      exit 2
      ;;
  esac
done

echo ""
echo "install-dev complete (scopes: $SCOPE)."
echo "For a full bootstrap: make install-full"
echo "Local loops: see docs/guides/developer-guide.md (K8s/Kind optional)."
