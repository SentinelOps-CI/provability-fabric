#!/usr/bin/env bash
set -euo pipefail

export TZ=UTC
export LC_ALL=C.UTF-8

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT/runner"
OUT_DIR="$ROOT_DIR/tests/replay/out"
CERT_DIR="$OUT_DIR/certs"
ENV_JSON="$ROOT_DIR/tests/replay/env.json"

mkdir -p "$CERT_DIR"

echo "Using TRACE-REPLAY-KIT at: $KIT_DIR"

# Build Docker image for reproducible runs
IMAGE_TAG="trace-replay-runner:kit"
docker build -t "$IMAGE_TAG" "$KIT_DIR"

# Number of repeated runs per bundle (higher on scheduled CI)
REPLAY_RUNS="${REPLAY_RUNS:-3}"
LV_THRESHOLD="${LOWVIEW_THRESHOLD:-0.999999}"

# Iterate bundles
for b in "$ROOT_DIR/tests/replay/bundles"/*; do
  [ -d "$b" ] || continue
  name=$(basename "$b")
  trace="$b/trace.json"
  fixtures="$b/fixtures"

  echo "Running replay for bundle: $name (runs=$REPLAY_RUNS)"
  for i in $(seq 1 "$REPLAY_RUNS"); do
    cert_out_host="$CERT_DIR/${name}_run${i}.cert.json"

    # Invoke runner inside container with mounted repo for deterministic env
    docker run --rm \
      -e TZ=UTC -e LC_ALL=C.UTF-8 \
      -v "$ROOT_DIR":/work \
      -w /work/external/TRACE-REPLAY-KIT/runner \
      "$IMAGE_TAG" bash replay_run.sh \
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

# Low-view determinism check (oracle)
python3 "$ROOT_DIR/external/TRACE-REPLAY-KIT/oracles/lowview_equal.py" \
  --input "$OUT_DIR" \
  --threshold "$LV_THRESHOLD"

echo "Replay runs complete. CERTs at $CERT_DIR"


