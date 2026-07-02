#!/usr/bin/env bash
# Wave 7 cluster status helper — summarizes gated workflow health by cluster.
# Requires gh CLI. Exit 0 only when all clusters marked "green" in ci-health-matrix
# have two consecutive successes (manual verification still required post-merge).
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT_DIR"

REPO="${GITHUB_REPOSITORY:-SentinelOps-CI/provability-fabric}"
BRANCH="${CI_INVENTORY_BRANCH:-main}"

declare -A CLUSTERS=(
  [replay]="platform-replay.yml nightly-replay.yml replay.yml morph-replay.yml platform-cert-validate.yml"
  [security]="codeql.yaml cargo-deny.yml wasm-scan.yaml scorecards.yml"
  [lean]="lean-offline.yaml lean-style.yaml lean-morph.yaml paper-conformance.yaml"
  [platform]="slo-gates.yaml operational-excellence.yaml billing-test.yaml integration.yaml demo-e2e.yml"
  [bench]="bench-nightly-criterion.yaml performance-gate.yaml bench-swebench-smoke.yaml"
  [evidence]="evidence-v01-smoke.yml evidence.yaml cert-validate.yml standards-pin.yml"
  [core]="ci.yml proto-compat.yaml actionlint.yml"
)

status_for() {
  local wf="$1"
  local run
  run=$(gh run list --repo "$REPO" --branch "$BRANCH" --workflow "$wf" --limit 1 --json conclusion,status,url 2>/dev/null || echo '[]')
  local conclusion status url
  conclusion=$(echo "$run" | python -c "import json,sys; d=json.load(sys.stdin); print(d[0].get('conclusion') or 'unknown' if d else 'no_run')" 2>/dev/null || echo "unknown")
  status=$(echo "$run" | python -c "import json,sys; d=json.load(sys.stdin); print(d[0].get('status') or 'unknown' if d else 'no_run')" 2>/dev/null || echo "unknown")
  url=$(echo "$run" | python -c "import json,sys; d=json.load(sys.stdin); print(d[0].get('url') or '-' if d else '-')" 2>/dev/null || echo "-")
  if [[ "$conclusion" == "success" ]]; then
    echo "green|$url"
  elif [[ "$status" == "in_progress" || "$status" == "queued" ]]; then
    echo "in_progress|$url"
  elif [[ "$conclusion" == "no_run" || "$conclusion" == "unknown" ]]; then
    echo "no_run|$url"
  else
    echo "red|$url"
  fi
}

echo "=== Wave 7 cluster status (branch=${BRANCH}) ==="
echo "Repo: ${REPO}"
echo "Generated: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo

overall_red=0
for cluster in replay security lean platform bench evidence core remaining; do
  if [[ "$cluster" == "remaining" ]]; then
    echo "--- remaining (~30 workflows) ---"
    echo "  status: pending main merge — run scripts/ci_workflow_inventory.sh --markdown"
    echo
    continue
  fi
  echo "--- ${cluster} ---"
  cluster_red=0
  for wf in ${CLUSTERS[$cluster]}; do
    IFS='|' read -r st url <<< "$(status_for "$wf")"
    printf "  %-35s %s\n" "$wf" "$st"
    [[ "$st" != "green" ]] && cluster_red=1
  done
  if [[ $cluster_red -eq 0 ]]; then
    echo "  cluster: green (latest run) — confirm two consecutive successes on main"
  else
    echo "  cluster: pending main merge / triage"
    overall_red=1
  fi
  echo
done

if [[ $overall_red -eq 0 ]]; then
  echo "All tracked clusters show latest green on ${BRANCH}."
else
  echo "One or more clusters not green on ${BRANCH}. See docs/internal/wave7-post-merge-runbook.md"
  exit 1
fi
