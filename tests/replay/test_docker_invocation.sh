#!/usr/bin/env bash
# Contract test: Docker replay runner must accept CLI args directly (F10).
# Image ENTRYPOINT is `python replay_run.py`; do NOT pass `bash replay_run.sh`.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT/runner"
IMAGE_TAG="trace-replay-runner:contract-test"
OUT_DIR="$ROOT_DIR/tests/replay/out/contract"
CERT_OUT="$OUT_DIR/contract.cert.json"

if ! command -v docker >/dev/null 2>&1; then
  echo "SKIP: docker not available" >&2
  exit 0
fi

if [[ ! -f "$KIT_DIR/replay_run.py" ]]; then
  echo "SKIP: TRACE-REPLAY-KIT submodule not initialized ($KIT_DIR)" >&2
  exit 0
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

echo "Running contract invocation for bundle: $name"
docker run --rm \
  -e TZ=UTC -e LC_ALL=C.UTF-8 \
  -v "$ROOT_DIR":/work \
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
