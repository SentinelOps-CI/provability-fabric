#!/usr/bin/env bash
# Freeze LabTrust + CertifyEdge release fixtures for PF verification gate.
# Certified bundle: LabTrust-Gym/examples/pcs_qc_release/release/science_claim_bundle.certified.json
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"

PARENT="$(cd "${ROOT}/.." && pwd)"
RELEASE="${ROOT}/tests/pcs/fixtures/labtrust-release"
PCS_CORE="${PCS_CORE_PATH:-${PARENT}/pcs-core}"
PCS_CORE_RELEASE="${PCS_CORE}/examples/labtrust-release"
LABTRUST="${LABTRUST_GYM_ROOT:-${PARENT}/LabTrust-Gym}"
CERTIFIED_SRC="${LABTRUST}/examples/pcs_qc_release/release/science_claim_bundle.certified.json"
CERTIFIED="${RELEASE}/science_claim_bundle.certified.json"
VR="${RELEASE}/verification_result.json"
SIGNED="${RELEASE}/signed_science_claim_bundle.json"
MANIFEST="${RELEASE}/FIXTURE_MANIFEST.json"
PCS="${PCS:-${ROOT}/scripts/pcs}"

mkdir -p "${RELEASE}"
if [[ ! -f "${CERTIFIED_SRC}" ]]; then
  echo "error: LabTrust release certified bundle not found: ${CERTIFIED_SRC}" >&2
  exit 1
fi

PF_SOURCE_COMMIT="$(git -C "${ROOT}" rev-parse HEAD)"
export PF_SOURCE_COMMIT
export PF_RELEASE_MODE=1
export PF_DETERMINISTIC="${PF_DETERMINISTIC:-1}"

if python3 -c "import sys; sys.exit(0 if '${PF_SOURCE_COMMIT}' not in {
'0000000000000000000000000000000000000000',
'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
'cccccccccccccccccccccccccccccccccccccccc',
'dddddddddddddddddddddddddddddddddddddddd',
'eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee',
} else 1)"; then
  : "ok"
else
  echo "error: PF_SOURCE_COMMIT is a forbidden placeholder: ${PF_SOURCE_COMMIT}" >&2
  exit 1
fi

cp "${CERTIFIED_SRC}" "${CERTIFIED}"
echo "Copied certified bundle from LabTrust-Gym release"

python3 "${ROOT}/scripts/pcs-freeze-labtrust-release-invalid.py" "${RELEASE}"

if ! rebuild_pf "${ROOT}"; then
  exit 2
fi

run_pf verify science-claim "${CERTIFIED}" --release-mode --out "${VR}"
run_pf sign science-claim "${CERTIFIED}" --release-mode --out "${SIGNED}"
run_pf inspect science-claim "${SIGNED}" --strict
run_pf validate verification-result "${VR}"
run_pf validate signed-science-claim "${SIGNED}"

if [[ -f "${PCS}" ]]; then
  "${PCS}" validate "${CERTIFIED}"
  "${PCS}" validate "${VR}"
  "${PCS}" validate "${SIGNED}"
fi

python3 - "${MANIFEST}" "${PF_SOURCE_COMMIT}" <<'PY'
import json, pathlib, sys
manifest_path, pf_commit = sys.argv[1:3]
manifest = {}
p = pathlib.Path(manifest_path)
if p.exists():
    manifest = json.loads(p.read_text(encoding="utf-8"))
manifest["pf_source_commit"] = pf_commit
manifest["regenerate"] = "make freeze-pcs-labtrust-release"
manifest.pop("deterministic_env", None)
p.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
PY

if [[ -d "${PCS_CORE}/examples/labtrust-release" ]]; then
  python3 "${ROOT}/scripts/pcs-sync-pcs-core-release.py" "${RELEASE}" "${PCS_CORE_RELEASE}" "${PF_SOURCE_COMMIT}"
fi

echo "OK: labtrust-release fixtures frozen (pf_source_commit=${PF_SOURCE_COMMIT})"
