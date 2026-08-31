#!/usr/bin/env bash
set -euo pipefail

export TZ=UTC
export LC_ALL=C.UTF-8

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT/runner"
OUT_DIR="$ROOT_DIR/tests/replay/out"
CERT_DIR="$OUT_DIR/certs"
OVERLAY_RUNNER="$ROOT_DIR/tests/replay/overlays/replay_run.py"
# Replay certificates use the Evidence v0.2 trace-replay schema, not the runtime CERT-V1 shape.
DEFAULT_SCHEMA="/work/specs/evidence/v0.2/schemas/trace-replay-cert.schema.json"
HOST_DEFAULT_SCHEMA="$ROOT_DIR/specs/evidence/v0.2/schemas/trace-replay-cert.schema.json"
TRACE_REPLAY_SCHEMA_PATH="${TRACE_REPLAY_SCHEMA_PATH:-$DEFAULT_SCHEMA}"
TRACE_REPLAY_SCHEMA_REQUIRED="${TRACE_REPLAY_SCHEMA_REQUIRED:-1}"

if [[ "$TRACE_REPLAY_SCHEMA_PATH" == "$DEFAULT_SCHEMA" && ! -f "$HOST_DEFAULT_SCHEMA" ]]; then
  echo "Error: trace replay schema missing at $HOST_DEFAULT_SCHEMA" >&2
  exit 1
fi

rm -rf "$CERT_DIR"
mkdir -p "$CERT_DIR"

echo "Using TRACE-REPLAY-KIT at: $KIT_DIR"

if [ ! -f "$OVERLAY_RUNNER" ]; then
  echo "Error: missing runner overlay at $OVERLAY_RUNNER" >&2
  exit 1
fi

# Build Docker image for reproducible runs
IMAGE_TAG="trace-replay-runner:kit"
docker build -t "$IMAGE_TAG" "$KIT_DIR"

# Overlay replay_run.py fail-closes date-time format checks. The KIT image only
# installs KIT runner requirements (jsonschema without rfc3339-validator).
# Layer the checked-in cert-validate extras into the same runtime image used
# by docker run. Fail closed if the extra cannot be imported.
CERT_VALIDATE_REQ="$ROOT_DIR/tools/cert-validate/requirements.txt"
if [[ ! -f "$CERT_VALIDATE_REQ" ]]; then
  echo "Error: missing $CERT_VALIDATE_REQ" >&2
  exit 1
fi
fmt_name="pf-kit-fmt-$$"
docker rm -f "$fmt_name" >/dev/null 2>&1 || true
if ! docker run --name "$fmt_name" --entrypoint python \
  -v "$CERT_VALIDATE_REQ":/tmp/cert-validate-requirements.txt:ro \
  "$IMAGE_TAG" \
  -m pip install --no-cache-dir -r /tmp/cert-validate-requirements.txt; then
  docker rm -f "$fmt_name" >/dev/null 2>&1 || true
  echo "Error: failed to install fail-closed date-time extras into $IMAGE_TAG" >&2
  exit 1
fi
docker commit "$fmt_name" "$IMAGE_TAG" >/dev/null
docker rm -f "$fmt_name" >/dev/null 2>&1 || true
if ! docker run --rm --entrypoint python "$IMAGE_TAG" -c \
  "import rfc3339_validator, jsonschema"; then
  echo "Error: $IMAGE_TAG cannot import rfc3339_validator after install" >&2
  exit 1
fi

# Number of repeated runs per bundle (higher on scheduled CI)
REPLAY_RUNS="${REPLAY_RUNS:-3}"
LV_THRESHOLD="${LOWVIEW_THRESHOLD:-0.999}"

# Iterate bundles
for b in "$ROOT_DIR/tests/replay/bundles"/*; do
  [ -d "$b" ] || continue
  name=$(basename "$b")
  echo "Running replay for bundle: $name (runs=$REPLAY_RUNS)"
  for i in $(seq 1 "$REPLAY_RUNS"); do
    # Invoke runner inside container with mounted repo for deterministic env.
    # ENTRYPOINT is `python replay_run.py` with -w set to the KIT runner dir, so the
    # overlay must replace that path (not /app/replay_run.py alone).
    docker run --rm \
      -e TZ=UTC -e LC_ALL=C.UTF-8 \
      -e TRACE_REPLAY_SCHEMA_PATH="$TRACE_REPLAY_SCHEMA_PATH" \
      -e TRACE_REPLAY_SCHEMA_REQUIRED="$TRACE_REPLAY_SCHEMA_REQUIRED" \
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


