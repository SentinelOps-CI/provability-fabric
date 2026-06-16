#!/usr/bin/env bash
# ci_workflow_inventory.sh — list workflow files and verify last main run is success
# for every workflow that triggers on push or schedule.
#
# Usage:
#   scripts/ci_workflow_inventory.sh [--list-only]
#
# Environment:
#   GITHUB_REPOSITORY  default: SentinelOps-CI/provability-fabric
#   CI_INVENTORY_BRANCH default: main
#
# Exit 0 when all gated workflows have conclusion=success on the last main run.
# Exit 1 when any gated workflow is missing a run or last run is not success.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)
WF_DIR="$ROOT_DIR/.github/workflows"
REPO="${GITHUB_REPOSITORY:-SentinelOps-CI/provability-fabric}"
BRANCH="${CI_INVENTORY_BRANCH:-main}"
LIST_ONLY=0

if [[ "${1:-}" == "--list-only" ]]; then
  LIST_ONLY=1
fi

if ! command -v gh >/dev/null 2>&1; then
  echo "error: gh CLI is required" >&2
  exit 2
fi

# Returns 0 when the workflow file declares push and/or schedule under on:.
workflow_has_push_or_schedule() {
  local file="$1"
  if grep -qE '^[[:space:]]*(push|schedule):' "$file"; then
    return 0
  fi
  if grep -qE '^on:[[:space:]]*\[.*\b(push|schedule)\b' "$file"; then
    return 0
  fi
  return 1
}

format_triggers() {
  local file="$1"
  local triggers=()
  for t in push pull_request pull_request_target schedule release workflow_dispatch workflow_call issue_comment; do
    if grep -qE "^[[:space:]]*${t}:" "$file" || grep -qE "^on:[[:space:]]*\[.*\b${t}\b" "$file"; then
      triggers+=("$t")
    fi
  done
  if ((${#triggers[@]} == 0)); then
    echo "—"
  else
    local IFS=', '
    echo "${triggers[*]}"
  fi
}

query_last_main_run() {
  local workflow_file="$1"
  gh run list \
    --repo "$REPO" \
    --workflow "$workflow_file" \
    --branch "$BRANCH" \
    --limit 1 \
    --json conclusion,status,url \
    --jq 'if length == 0 then "no_run|—" else "\(.[0].conclusion // .[0].status // "unknown")|\(.[0].url // "—")" end' 2>/dev/null || echo "no_run|—"
}

total=0
gated=0
green=0
red=0
unknown=0
failures=()

printf "CI workflow inventory — repo=%s branch=%s\n" "$REPO" "$BRANCH"
printf "%-42s %-28s %-12s %s\n" "WORKFLOW" "TRIGGERS" "STATUS" "URL"
printf '%0.s-' {1..110}
echo

shopt -s nullglob
for wf in "$WF_DIR"/*.yml "$WF_DIR"/*.yaml; do
  [[ -f "$wf" ]] || continue
  fname=$(basename "$wf")
  total=$((total + 1))
  triggers=$(format_triggers "$wf")

  result=$(query_last_main_run "$fname")
  status="${result%%|*}"
  url="${result#*|}"

  case "$status" in
    success) color="green"; green=$((green + 1)) ;;
    no_run|unknown|"") color="unknown"; unknown=$((unknown + 1)) ;;
    *) color="red"; red=$((red + 1)) ;;
  esac

  gate=""
  if workflow_has_push_or_schedule "$wf"; then
    gated=$((gated + 1))
    gate="*"
    if [[ "$status" != "success" ]]; then
      failures+=("$fname ($status)")
    fi
  fi

  printf "%-42s %-28s %-12s %s\n" "$fname" "$triggers" "${status}${gate}" "$url"
done

echo
echo "Summary: total=$total gated(push/schedule)=$gated green=$green red=$red unknown=$unknown"

if [[ "$LIST_ONLY" -eq 1 ]]; then
  exit 0
fi

if ((${#failures[@]} > 0)); then
  echo
  echo "Gated workflows not green on last $BRANCH run:" >&2
  for f in "${failures[@]}"; do
    echo "  - $f" >&2
  done
  exit 1
fi

exit 0
