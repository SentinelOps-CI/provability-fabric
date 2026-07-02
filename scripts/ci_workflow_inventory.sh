#!/usr/bin/env bash
# ci_workflow_inventory.sh — list workflow files and verify last main run is success
# for every workflow that triggers on push or schedule.
#
# Usage:
#   scripts/ci_workflow_inventory.sh [--list-only]
#   pwsh scripts/ci_workflow_inventory.ps1 [-ListOnly]   # Windows native [--markdown [FILE]]
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
MARKDOWN=0
MARKDOWN_FILE=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --list-only)
      LIST_ONLY=1
      shift
      ;;
    --markdown)
      MARKDOWN=1
      if [[ "${2:-}" != "" && "${2:0:1}" != "-" ]]; then
        MARKDOWN_FILE="$2"
        shift
      else
        MARKDOWN_FILE="$ROOT_DIR/docs/internal/ci-inventory-latest.md"
      fi
      shift
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

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

# Collect rows for markdown output
declare -a MD_ROWS=()

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
  gated_flag=""
  if workflow_has_push_or_schedule "$wf"; then
    gated=$((gated + 1))
    gate="*"
    gated_flag="yes"
    if [[ "$status" != "success" ]]; then
      failures+=("$fname ($status)")
    fi
  else
    gated_flag="no"
  fi

  printf "%-42s %-28s %-12s %s\n" "$fname" "$triggers" "${status}${gate}" "$url"
  MD_ROWS+=("$fname|$triggers|$status|$gated_flag|$url")
done

echo
echo "Summary: total=$total gated(push/schedule)=$gated green=$green red=$red unknown=$unknown"

if [[ "$MARKDOWN" -eq 1 ]]; then
  generated_at=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
  {
    echo "# CI workflow inventory (auto-generated)"
    echo ""
    echo "Generated: ${generated_at} UTC"
    echo "Repository: \`${REPO}\` branch \`${BRANCH}\`"
    echo ""
    echo "## Summary"
    echo ""
    echo "| Metric | Count |"
    echo "|--------|------:|"
    echo "| Total workflow files | ${total} |"
    echo "| Gated (push/schedule on main) | ${gated} |"
    echo "| Green (last run success) | ${green} |"
    echo "| Red (failure/cancelled/in progress) | ${red} |"
    echo "| No run / unknown | ${unknown} |"
    echo ""
    echo "## Workflows"
    echo ""
    echo "| Workflow | Triggers | Last status | Gated | URL |"
    echo "|----------|----------|-------------|-------|-----|"
    for row in "${MD_ROWS[@]}"; do
      IFS='|' read -r wf_name wf_triggers wf_status wf_gated wf_url <<< "$row"
      if [[ "$wf_gated" == "yes" && "$wf_status" != "success" ]]; then
        wf_status="**${wf_status}**"
      fi
      echo "| \`${wf_name}\` | ${wf_triggers} | ${wf_status} | ${wf_gated} | ${wf_url} |"
    done
    if ((${#failures[@]} > 0)); then
      echo ""
      echo "## Gated workflows not green"
      echo ""
      for f in "${failures[@]}"; do
        echo "- \`${f}\`"
      done
    fi
  } > "$MARKDOWN_FILE"
  echo "Markdown report written to $MARKDOWN_FILE"
fi

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
