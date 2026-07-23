#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Blue/green DB migration helper.
#   --dry-run       Plan only (CI / moto floor)
#   --verify-only   Live connectivity + Route53 read; no mutations (Wave 13 live DR)
#   --confirm       Apply schema to green + Route53 UPSERT to green host (ops)

set -euo pipefail

DRY_RUN=0
VERIFY_ONLY=0
CONFIRM=0
BLUE_DB_URL=""
GREEN_DB_URL=""
DNS_ZONE=""
DNS_RECORD=""
SMOKE_TEST_URL=""

usage() {
  cat <<'EOF'
Usage: blue_green_migrate.sh [options]
  --dry-run                 Plan only; no DNS or schema mutations
  --verify-only             Live connectivity + Route53 read checks; no mutations
  --confirm                 Allow live mutation path (schema apply + DNS flip)
  --blue-db-url URL         Blue (current) Postgres URL
  --green-db-url URL        Green (target) Postgres URL
  --dns-zone ZONE_ID        Route53 hosted zone id
  --dns-record NAME         DNS record to flip (e.g. db.example.com)
  --smoke-test-url URL      Optional post-flip health URL

Mutation env (optional):
  PF_BG_MIGRATE_CMD         Shell command run with DATABASE_URL=green (preferred)
  PF_BG_DNS_TYPE            Route53 record type (default CNAME)
  PF_BG_DNS_TTL             TTL seconds (default 60)
  PF_BG_DNS_VALUE           Explicit DNS target (default: host from --green-db-url)
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run) DRY_RUN=1; shift ;;
    --verify-only) VERIFY_ONLY=1; shift ;;
    --confirm) CONFIRM=1; shift ;;
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
echo "dry_run=$DRY_RUN verify_only=$VERIFY_ONLY confirm=$CONFIRM"
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

host_from_url() {
  echo "$1" | sed -E 's|^[a-zA-Z][a-zA-Z0-9+.-]*://||; s|^[^@]*@||; s|/.*||; s|:.*||'
}

if [[ "$DRY_RUN" -eq 1 ]]; then
  plan
  echo "dry-run complete (no mutations)"
  exit 0
fi

if ! command -v aws >/dev/null 2>&1; then
  echo "error: aws CLI required for live migration" >&2
  exit 1
fi
if ! command -v pg_isready >/dev/null 2>&1; then
  echo "error: pg_isready required for live migration" >&2
  exit 1
fi

blue_host=$(host_from_url "$BLUE_DB_URL")
green_host=$(host_from_url "$GREEN_DB_URL")

pg_isready -h "$blue_host" -p 5432
pg_isready -h "$green_host" -p 5432

# Non-simulated Route53 presence check (read-only)
aws route53 list-resource-record-sets \
  --hosted-zone-id "$DNS_ZONE" \
  --query "ResourceRecordSets[?Name==\`${DNS_RECORD}.\` || Name==\`${DNS_RECORD}\`]" \
  --output json | grep -q "$DNS_RECORD"

if [[ -n "$SMOKE_TEST_URL" ]]; then
  curl -fsS "$SMOKE_TEST_URL" >/dev/null
fi

if [[ "$VERIFY_ONLY" -eq 1 ]]; then
  echo "verify-only complete (live connectivity + Route53 read; no mutations)"
  exit 0
fi

if [[ "$CONFIRM" -ne 1 ]]; then
  echo "live migration steps require --confirm (or use --verify-only / --dry-run)" >&2
  echo "fail-closed: refusing schema apply / DNS flip without --confirm" >&2
  exit 1
fi

echo "== live mutation: schema apply on green =="
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [[ -n "${PF_BG_MIGRATE_CMD:-}" ]]; then
  echo "running PF_BG_MIGRATE_CMD against green"
  DATABASE_URL="$GREEN_DB_URL" bash -c "$PF_BG_MIGRATE_CMD"
elif [[ -d "$REPO_ROOT/runtime/ledger/prisma" ]] && command -v npx >/dev/null 2>&1; then
  echo "running prisma migrate deploy (runtime/ledger) against green"
  (
    cd "$REPO_ROOT/runtime/ledger"
    DATABASE_URL="$GREEN_DB_URL" npx prisma migrate deploy
  )
else
  echo "error: no migration runner; set PF_BG_MIGRATE_CMD or install prisma under runtime/ledger" >&2
  exit 1
fi

if [[ -n "$SMOKE_TEST_URL" ]]; then
  echo "== smoke before DNS flip =="
  curl -fsS "$SMOKE_TEST_URL" >/dev/null
fi

DNS_TYPE="${PF_BG_DNS_TYPE:-CNAME}"
DNS_TTL="${PF_BG_DNS_TTL:-60}"
DNS_VALUE="${PF_BG_DNS_VALUE:-$green_host}"
# CNAME targets must be FQDNs ending in a dot for Route53.
if [[ "$DNS_TYPE" == "CNAME" && "${DNS_VALUE: -1}" != "." ]]; then
  DNS_VALUE="${DNS_VALUE}."
fi
RECORD_NAME="$DNS_RECORD"
if [[ "${RECORD_NAME: -1}" != "." ]]; then
  RECORD_NAME="${RECORD_NAME}."
fi

CHANGE_BATCH="$(mktemp)"
trap 'rm -f "$CHANGE_BATCH"' EXIT
cat >"$CHANGE_BATCH" <<EOF
{
  "Comment": "blue/green flip to green via blue_green_migrate.sh",
  "Changes": [{
    "Action": "UPSERT",
    "ResourceRecordSet": {
      "Name": "${RECORD_NAME}",
      "Type": "${DNS_TYPE}",
      "TTL": ${DNS_TTL},
      "ResourceRecords": [{"Value": "${DNS_VALUE}"}]
    }
  }]
}
EOF

echo "== live mutation: Route53 UPSERT $RECORD_NAME → $DNS_VALUE ($DNS_TYPE) =="
CHANGE_ID=$(aws route53 change-resource-record-sets \
  --hosted-zone-id "$DNS_ZONE" \
  --change-batch "file://${CHANGE_BATCH}" \
  --query 'ChangeInfo.Id' \
  --output text)
echo "route53 change_id=$CHANGE_ID"
aws route53 wait resource-record-sets-changed --id "$CHANGE_ID"

if [[ -n "$SMOKE_TEST_URL" ]]; then
  echo "== smoke after DNS flip =="
  curl -fsS "$SMOKE_TEST_URL" >/dev/null
fi

echo "live mutation complete (schema apply + DNS flip)"
exit 0
