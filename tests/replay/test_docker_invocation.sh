#!/usr/bin/env bash
# Contract test: Docker replay runner must accept CLI args directly (F10).
# Image ENTRYPOINT is `python replay_run.py`; do NOT pass `bash replay_run.sh`.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT/runner"
OVERLAY_RUNNER="$ROOT_DIR/tests/replay/overlays/replay_run.py"
IMAGE_TAG="trace-replay-runner:contract-test"
OUT_DIR="$ROOT_DIR/tests/replay/out/contract"
CERT_OUT="$OUT_DIR/contract.cert.json"
CERT_VALIDATE_REQ="$ROOT_DIR/tools/cert-validate/requirements.txt"

if ! command -v docker >/dev/null 2>&1; then
  echo "SKIP: docker not available" >&2
  exit 0
fi

if [[ ! -f "$KIT_DIR/replay_run.py" ]]; then
  echo "SKIP: TRACE-REPLAY-KIT submodule not initialized ($KIT_DIR)" >&2
  exit 0
fi

if [[ ! -f "$OVERLAY_RUNNER" ]]; then
  echo "error: missing runner overlay at $OVERLAY_RUNNER" >&2
  exit 1
fi

if [[ ! -f "$CERT_VALIDATE_REQ" ]]; then
  echo "error: missing $CERT_VALIDATE_REQ" >&2
  exit 1
fi

BUNDLE=""
for b in "$ROOT_DIR/tests/replay/bundles"/*; do
  [[ -d "$b" ]] || continue
  BUNDLE="$b"
  break
done

if [[ -z "$BUNDLE" ]]; then
  echo "error: no replay bundle under tests/replay/bundles" >&2
  exit 1
fi

name=$(basename "$BUNDLE")
mkdir -p "$OUT_DIR"

echo "Building replay runner image: $IMAGE_TAG"
docker build -t "$IMAGE_TAG" "$KIT_DIR"

fmt_name="pf-contract-fmt-$$"
docker rm -f "$fmt_name" >/dev/null 2>&1 || true
if ! docker run --name "$fmt_name" --entrypoint python \
  -v "$CERT_VALIDATE_REQ":/tmp/cert-validate-requirements.txt:ro \
  "$IMAGE_TAG" \
  -m pip install --no-cache-dir -r /tmp/cert-validate-requirements.txt; then
  docker rm -f "$fmt_name" >/dev/null 2>&1 || true
  echo "error: failed to install fail-closed date-time extras into $IMAGE_TAG" >&2
  exit 1
fi
docker commit \
  --change 'ENTRYPOINT ["python", "replay_run.py"]' \
  --change 'CMD []' \
  "$fmt_name" "$IMAGE_TAG" >/dev/null
docker rm -f "$fmt_name" >/dev/null 2>&1 || true

echo "Running contract invocation for bundle: $name"
docker run --rm \
  -e TZ=UTC -e LC_ALL=C.UTF-8 \
  -e TRACE_REPLAY_SCHEMA_PATH=/work/specs/evidence/v0.2/schemas/trace-replay-cert.schema.json \
  -e TRACE_REPLAY_SCHEMA_REQUIRED=1 \
  -v "$ROOT_DIR":/work \
  -v "$OVERLAY_RUNNER":/work/external/TRACE-REPLAY-KIT/runner/replay_run.py:ro \
  -w /work/external/TRACE-REPLAY-KIT/runner \
  "$IMAGE_TAG" \
    --bundle "/work/tests/replay/bundles/$name" \
    --trace "/work/tests/replay/bundles/$name/trace.json" \
    --fixtures "/work/tests/replay/bundles/$name/fixtures" \
    --cert-out "/work/tests/replay/out/contract/${name}.cert.json"

if [[ ! -f "$OUT_DIR/${name}.cert.json" ]]; then
  echo "error: expected CERT at $OUT_DIR/${name}.cert.json" >&2
  exit 1
fi

# Negative: shell wrapper must NOT be passed as Python args
set +e
err=$(docker run --rm "$IMAGE_TAG" bash replay_run.sh 2>&1)
rc=$?
set -e
if [[ $rc -eq 0 ]]; then
  echo "error: bash replay_run.sh should fail when passed to python entrypoint" >&2
  exit 1
fi
if ! echo "$err" | grep -Eqi "unrecognized arguments|required: --trace|required: --fixtures|error:"; then
  echo "error: bad invocation should fail argparse, got: $err" >&2
  exit 1
fi

echo "Docker replay invocation contract: OK"
