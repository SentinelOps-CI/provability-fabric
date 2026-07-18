#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Blue/green DB migration helper. Supports --dry-run for CI (no AWS mutations).

set -euo pipefail

DRY_RUN=0
BLUE_DB_URL=""
GREEN_DB_URL=""
DNS_ZONE=""
DNS_RECORD=""
SMOKE_TEST_URL=""

usage() {
  cat <<'EOF'
Usage: blue_green_migrate.sh [options]
  --dry-run                 Plan only; no DNS or schema mutations
  --blue-db-url URL         Blue (current) Postgres URL
  --green-db-url URL        Green (target) Postgres URL
  --dns-zone ZONE_ID        Route53 hosted zone id
  --dns-record NAME         DNS record to flip
  --smoke-test-url URL      Optional post-flip health URL
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run) DRY_RUN=1; shift ;;
    --blue-db-url) BLUE_DB_URL="$2"; shift 2 ;;
    --green-db-url) GREEN_DB_URL="$2"; shift 2 ;;
    --dns-zone) DNS_ZONE="$2"; shift 2 ;;
    --dns-record) DNS_RECORD="$2"; shift 2 ;;
    --smoke-test-url) SMOKE_TEST_URL="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ -z "$BLUE_DB_URL" || -z "$GREEN_DB_URL" || -z "$DNS_ZONE" || -z "$DNS_RECORD" ]]; then
  echo "error: --blue-db-url, --green-db-url, --dns-zone, and --dns-record are required" >&2
  exit 2
fi

echo "== blue/green migrate =="
echo "dry_run=$DRY_RUN"
echo "blue=$BLUE_DB_URL"
echo "green=$GREEN_DB_URL"
echo "dns_zone=$DNS_ZONE dns_record=$DNS_RECORD"
[[ -n "$SMOKE_TEST_URL" ]] && echo "smoke=$SMOKE_TEST_URL"

plan() {
  echo "[plan] 1. verify blue connectivity"
  echo "[plan] 2. verify green connectivity"
  echo "[plan] 3. apply migrations to green"
  echo "[plan] 4. smoke-test green"
  echo "[plan] 5. flip Route53 $DNS_RECORD in zone $DNS_ZONE to green"
  echo "[plan] 6. final health verification"
}

if [[ "$DRY_RUN" -eq 1 ]]; then
  plan
  echo "dry-run complete (no mutations)"
  exit 0
fi

# Live path requires aws + pg tooling; keep fail-closed if invoked without dry-run
# in environments that lack secrets/infra.
if ! command -v aws >/dev/null 2>&1; then
  echo "error: aws CLI required for live migration" >&2
  exit 1
fi
if ! command -v pg_isready >/dev/null 2>&1; then
  echo "error: pg_isready required for live migration" >&2
  exit 1
fi

# Parse host from URL for pg_isready (best-effort)
blue_host=$(echo "$BLUE_DB_URL" | sed -E 's|.*@([^:/]+).*|\1|')
green_host=$(echo "$GREEN_DB_URL" | sed -E 's|.*@([^:/]+).*|\1|')

pg_isready -h "$blue_host" -p 5432
pg_isready -h "$green_host" -p 5432

if [[ -n "$SMOKE_TEST_URL" ]]; then
  curl -fsS "$SMOKE_TEST_URL" >/dev/null
fi

echo "live migration steps require operator confirmation of schema apply; aborting without --confirm"
echo "use --dry-run in CI; live flips are production-gated"
exit 1
