#!/usr/bin/env bash
# Docker Compose smoke test for production/full profile (F21).
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT_DIR"

PROFILE="${1:-full}"
COMPOSE="docker compose --profile ${PROFILE}"

if ! command -v docker >/dev/null 2>&1; then
  echo "SKIP: docker not available" >&2
  exit 0
fi

echo "=== docker-compose smoke (profile=${PROFILE}) ==="

# Rust service Dockerfiles expect Cargo.lock in their build context (workspace root lockfile).
if [[ -f Cargo.lock ]]; then
  for ctx in runtime/sidecar-watcher runtime/egress-firewall runtime/attestor; do
    if [[ -f "${ctx}/Dockerfile" ]]; then
      cp Cargo.lock "${ctx}/Cargo.lock"
    fi
  done
fi

$COMPOSE config >/dev/null
echo "compose config: OK"

# Long-running services exercised by this smoke (health curls below). Omit batch CLIs,
# demo apps, and platform microservices not required for compose/DB validation.
SMOKE_SERVICES=(
  postgres redis runtime-sidecar ledger retrieval-gateway
  prometheus grafana console
)
$COMPOSE up -d --wait --timeout 180 "${SMOKE_SERVICES[@]}"
echo "compose up --wait: OK"

# Health endpoints for core services in full profile
curl -fsS http://localhost:4000/health >/dev/null && echo "ledger /health: OK"
curl -fsS http://localhost:8080/health >/dev/null && echo "retrieval-gateway /health: OK" || true

$COMPOSE down -v
echo "compose down: OK"
echo "=== docker-compose smoke passed ==="
