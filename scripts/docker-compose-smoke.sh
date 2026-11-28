#!/usr/bin/env bash
# Docker Compose full-profile smoke: disposable credentials only.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT_DIR"

PROFILE="${1:-full}"
COMPOSE=(docker compose --profile "$PROFILE")

if ! command -v docker >/dev/null 2>&1; then
  echo "ERROR: docker is required to execute the Compose smoke" >&2
  exit 2
fi

echo "=== docker-compose smoke (profile=${PROFILE}) ==="

# Generate a disposable private key outside the source tree; never use production credentials.
if ! command -v openssl >/dev/null 2>&1; then
  echo "ERROR: openssl is required for disposable receipt signing" >&2
  exit 2
fi
SMOKE_KEY_DIR="$(mktemp -d)"
chmod 700 "$SMOKE_KEY_DIR"
SMOKE_COMPOSE_STARTED=0

cleanup() {
  status=$?
  trap - EXIT
  if [[ "$SMOKE_COMPOSE_STARTED" -eq 1 ]]; then
    "${COMPOSE[@]}" down -v >/dev/null 2>&1 ||
      echo "WARNING: failed to clean up smoke containers" >&2
  fi
  rm -rf -- "$SMOKE_KEY_DIR"
  exit "$status"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

export PF_RECEIPT_SIGNING_KEY_FILE="$SMOKE_KEY_DIR/retrieval-receipt.pem"
openssl genpkey -algorithm Ed25519 -out "$PF_RECEIPT_SIGNING_KEY_FILE" >/dev/null 2>&1
chmod 600 "$PF_RECEIPT_SIGNING_KEY_FILE"

# Independent ephemeral JWT issuer key: never reuse the receipt-signing key.
export PF_RETRIEVAL_JWT_SIGNING_KEY_FILE="$SMOKE_KEY_DIR/retrieval-jwt-issuer.pem"
openssl genpkey -algorithm Ed25519 -out "$PF_RETRIEVAL_JWT_SIGNING_KEY_FILE" >/dev/null 2>&1
chmod 600 "$PF_RETRIEVAL_JWT_SIGNING_KEY_FILE"
export PF_RETRIEVAL_JWT_ISSUER="pf-compose-smoke"
export PF_RETRIEVAL_JWT_VERIFY_KEYS_JSON
PF_RETRIEVAL_JWT_VERIFY_KEYS_JSON="$(python3 scripts/retrieval_auth_smoke.py export-public "$PF_RETRIEVAL_JWT_SIGNING_KEY_FILE")"
test -n "$PF_RETRIEVAL_JWT_VERIFY_KEYS_JSON" || { echo "Missing ephemeral JWT verifier" >&2; exit 2; }

python scripts/check_wiring.py

# Optional: validate documented env keys exist in schema (structural presence).
if [[ -f schemas/pf-env.schema.json ]]; then
  python - <<'PY'
import json, sys
from pathlib import Path
schema = json.loads(Path("schemas/pf-env.schema.json").read_text(encoding="utf-8"))
required_keys = {
    "PF_PROFILE", "PROFILE", "SIDECAR_URL", "LEDGER_URL", "KERNEL_URL", "PORT",
}
missing = required_keys - set(schema.get("properties", {}))
if missing:
    print(f"pf-env.schema.json missing properties: {sorted(missing)}", file=sys.stderr)
    sys.exit(1)
print("pf-env.schema.json: OK")
PY
fi

"${COMPOSE[@]}" config >/dev/null
echo "compose config: OK"

# Long-running services exercised by this smoke (health curls below). Omit batch CLIs,
# demo apps, and platform microservices not required for compose/DB validation.
SMOKE_SERVICES=(
  postgres redis runtime-sidecar ledger retrieval-gateway
)
SMOKE_COMPOSE_STARTED=1
"${COMPOSE[@]}" up -d --wait --timeout 180 "${SMOKE_SERVICES[@]}"
echo "compose up --wait: OK"

# Health endpoints for core services in full profile
curl -fsS http://localhost:4000/health >/dev/null
echo "ledger /health: OK"
curl -fsS http://localhost:8080/health >/dev/null
echo "retrieval-gateway /health: OK"

# Exercise the actual HTTP authorization boundary with disposable signed tokens.
# An unseeded index cannot establish data isolation; this only tests admission.
python3 scripts/retrieval_auth_smoke.py probe "$PF_RETRIEVAL_JWT_SIGNING_KEY_FILE"

"${COMPOSE[@]}" down -v
SMOKE_COMPOSE_STARTED=0
echo "compose down: OK"
echo "=== docker-compose smoke passed ==="
