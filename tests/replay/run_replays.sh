#!/usr/bin/env bash
set -euo pipefail

export TZ=UTC
export LC_ALL=C.UTF-8

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT/runner"
OUT_DIR="$ROOT_DIR/tests/replay/out"
CERT_DIR="$OUT_DIR/certs"
ENV_JSON="$ROOT_DIR/tests/replay/env.json"
OVERLAY_RUNNER="$ROOT_DIR/tests/replay/overlays/replay_run.py"
# Local fixture: upstream CERT-V1 raw URL 404s (private + wrong filename)
DEFAULT_SCHEMA="/work/tests/replay/schema/trace-replay-cert.schema.json"
CERT_V1_SCHEMA_PATH="${CERT_V1_SCHEMA_PATH:-$DEFAULT_SCHEMA}"

mkdir -p "$CERT_DIR"

echo "Using TRACE-REPLAY-KIT at: $KIT_DIR"

if [ ! -f "$OVERLAY_RUNNER" ]; then
  echo "Error: missing runner overlay at $OVERLAY_RUNNER" >&2
  exit 1
fi

# Build Docker image for reproducible runs
IMAGE_TAG="trace-replay-runner:kit"
docker build -t "$IMAGE_TAG" "$KIT_DIR"

# Number of repeated runs per bundle (higher on scheduled CI)
REPLAY_RUNS="${REPLAY_RUNS:-3}"
LV_THRESHOLD="${LOWVIEW_THRESHOLD:-0.999}"

# Iterate bundles
for b in "$ROOT_DIR/tests/replay/bundles"/*; do
  [ -d "$b" ] || continue
  name=$(basename "$b")
  trace="$b/trace.json"
  fixtures="$b/fixtures"

  echo "Running replay for bundle: $name (runs=$REPLAY_RUNS)"
  for i in $(seq 1 "$REPLAY_RUNS"); do
    cert_out_host="$CERT_DIR/${name}_run${i}.cert.json"

    # Invoke runner inside container with mounted repo for deterministic env.
    # ENTRYPOINT is `python replay_run.py` with -w set to the KIT runner dir, so the
    # overlay must replace that path (not /app/replay_run.py alone).
    docker run --rm \
      -e TZ=UTC -e LC_ALL=C.UTF-8 \
      -e CERT_V1_SCHEMA_PATH="$CERT_V1_SCHEMA_PATH" \
      -e CERT_V1_SCHEMA_REQUIRED="${CERT_V1_SCHEMA_REQUIRED:-0}" \
      -v "$ROOT_DIR":/work \
      -v "$OVERLAY_RUNNER":/work/external/TRACE-REPLAY-KIT/runner/replay_run.py:ro \
      -w /work/external/TRACE-REPLAY-KIT/runner \
      "$IMAGE_TAG" \
        --bundle "/work/tests/replay/bundles/$name" \
        --trace "/work/tests/replay/bundles/$name/trace.json" \
        --fixtures "/work/tests/replay/bundles/$name/fixtures" \
        --cert-out "/work/tests/replay/out/certs/${name}_run${i}.cert.json"
  done
done

# Ensure at least one cert was produced
shopt -s nullglob
CERT_COUNT=("$CERT_DIR"/*.cert.json)
if [ ${#CERT_COUNT[@]} -eq 0 ]; then
  echo "Error: No CERTs produced in $CERT_DIR" >&2
  exit 1
fi

# Low-view determinism per bundle (different traces may legitimately differ)
MIN_DETERMINISM=$(python3 -c "print(${LV_THRESHOLD} * 100)")
for b in "$ROOT_DIR/tests/replay/bundles"/*; do
  [ -d "$b" ] || continue
  name=$(basename "$b")
  shopt -s nullglob
  BUNDLE_CERTS=("$CERT_DIR/${name}_run"*.cert.json)
  if [ ${#BUNDLE_CERTS[@]} -lt 2 ]; then
    echo "Bundle $name: ${#BUNDLE_CERTS[@]} cert(s), skipping pairwise determinism"
    continue
  fi
  echo "Low-view determinism for bundle: $name"
  python3 "$ROOT_DIR/external/TRACE-REPLAY-KIT/oracles/lowview_equal.py" \
    "${BUNDLE_CERTS[@]}" \
    --min-determinism "$MIN_DETERMINISM"
done

echo "Replay runs complete. CERTs at $CERT_DIR"


