#!/usr/bin/env bash
set -euo pipefail
export PATH=/usr/local/go/bin:$PATH
apt-get update -qq && apt-get install -qq -y git python3 python3-pip >/dev/null 2>&1
git clone --depth 1 https://github.com/SentinelOps-CI/provability-fabric.git /pf
cd /pf
git clone --depth 1 --filter=blob:none --sparse https://github.com/SentinelOps-CI/pcs-core.git pcs-core
cd pcs-core && git sparse-checkout set schemas python examples/labtrust-release
cd /pf
python3 scripts/refresh-release-manifest-pins.py pcs-core/examples/labtrust-release
pip install -q --break-system-packages -e pcs-core/python
cd core/cli/pf
PF_COMMIT="$(python3 -c "import json;print(json.load(open('/pf/tests/pcs/fixtures/labtrust-release/FIXTURE_MANIFEST.json'))['pf_source_commit'])")"
export PF_SOURCE_COMMIT="$PF_COMMIT" PF_RELEASE_MODE=1 PF_ADMISSION_PROFILE=labtrust_qc_release
OUT=/tmp/rc.json
RC_DIR=/pf/pcs-core/examples/labtrust-release
MANIFEST="$RC_DIR/release_manifest.v0.json"
REGISTRY=/pf/tests/pcs/fixtures/labtrust-release/artifact_registry.json
go run . verify release-chain --manifest "$MANIFEST" --registry "$REGISTRY" --artifact-dir "$RC_DIR" --admission-profile labtrust_qc_release --release-mode --out "$OUT"
cat "$OUT" | head -40
pcs validate "$OUT" || true
