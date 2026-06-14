#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Initialize external/CERT-V1 and external/TRACE-REPLAY-KIT at pinned commits.
#
# CI: set STANDARDS_GITHUB_TOKEN (PAT with read access to verifiable-ai-ci/*).
# Local: SSH or HTTPS credentials, or the same token in your environment.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

VERSIONS_JSON="$ROOT/tools/standards/versions.json"
if [[ ! -f "$VERSIONS_JSON" ]]; then
  echo "Missing $VERSIONS_JSON" >&2
  exit 1
fi

read_pin() {
  python3 -c "
import json, sys
with open(sys.argv[1], encoding='utf-8') as f:
    pins = json.load(f)['pins']
print(pins[sys.argv[2]])
" "$VERSIONS_JSON" "$1"
}

CERT_COMMIT="$(read_pin CERT-V1)"
KIT_COMMIT="$(read_pin TRACE-REPLAY-KIT)"

cert_ok() {
  [[ -f external/CERT-V1/schema/cert-v1.schema.json ]]
}

kit_ok() {
  [[ -f external/TRACE-REPLAY-KIT/runner/replay_run.py ]]
}

head_at_pin() {
  local path="$1" expected="$2"
  [[ -d "$path/.git" ]] || return 1
  local head
  head="$(git -C "$path" rev-parse HEAD 2>/dev/null || true)"
  [[ "$head" == "$expected" ]]
}

if cert_ok && kit_ok && head_at_pin external/CERT-V1 "$CERT_COMMIT" && head_at_pin external/TRACE-REPLAY-KIT "$KIT_COMMIT"; then
  echo "External standards already at pinned commits."
  exit 0
fi

git_cfg=()
if [[ -n "${STANDARDS_GITHUB_TOKEN:-}" ]]; then
  git_cfg+=(-c "url.https://x-access-token:${STANDARDS_GITHUB_TOKEN}@github.com/.insteadOf=https://github.com/")
fi

try_submodule_init() {
  if [[ ! -f .gitmodules ]]; then
    return 1
  fi
  git "${git_cfg[@]}" submodule sync -- external/CERT-V1 external/TRACE-REPLAY-KIT
  git "${git_cfg[@]}" submodule update --init --depth 1 external/CERT-V1 external/TRACE-REPLAY-KIT
}

clone_at_pin() {
  local path="$1" url="$2" commit="$3"
  echo "Cloning $path at ${commit:0:12}..."
  rm -rf "$path"
  mkdir -p "$(dirname "$path")"
  git "${git_cfg[@]}" clone --filter=blob:none --no-checkout "$url" "$path"
  git -C "$path" fetch --depth 1 origin "$commit"
  git -C "$path" checkout FETCH_HEAD
}

if try_submodule_init && cert_ok && kit_ok; then
  echo "Submodules initialized."
  exit 0
fi

clone_at_pin external/CERT-V1 https://github.com/verifiable-ai-ci/CERT-V1.git "$CERT_COMMIT"
clone_at_pin external/TRACE-REPLAY-KIT https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT.git "$KIT_COMMIT"

if ! cert_ok || ! kit_ok; then
  echo "Failed to materialize external standards." >&2
  echo "For CI: configure STANDARDS_GITHUB_TOKEN with read access to verifiable-ai-ci/*." >&2
  exit 1
fi

echo "External standards ready."
