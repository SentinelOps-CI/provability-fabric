#!/usr/bin/env bash
# Atomically promote release-run/ PF artifacts to provability-fabric fixtures and pcs-core.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(cd "${ROOT}/.." && pwd)"
RUN="${PCS_RELEASE_RUN:-${ROOT}/release-run}"
PF_FIXTURES="${ROOT}/tests/pcs/fixtures/labtrust-release"
PCS_CORE_RELEASE="${PCS_CORE_PATH:-${PARENT}/pcs-core}/examples/labtrust-release"

for f in science_claim_bundle.certified.json verification_result.json signed_science_claim_bundle.json; do
  if [[ ! -f "${RUN}/${f}" ]]; then
    echo "error: missing ${RUN}/${f} (run scripts/pcs-release-run-pf.sh first)" >&2
    exit 1
  fi
done

python3 "${ROOT}/scripts/pcs-release-run-validate.py" "${RUN}"

PF_COMMIT="$(git -C "${ROOT}" rev-parse HEAD)"
MANIFEST="${RUN}/RELEASE_FIXTURE_MANIFEST.json"
if [[ -f "${MANIFEST}" ]]; then
  python3 - "${MANIFEST}" "${PF_COMMIT}" <<'PY'
import json, pathlib, sys
p, commit = pathlib.Path(sys.argv[1]), sys.argv[2]
m = json.loads(p.read_text(encoding="utf-8"))
m["provability_fabric_commit"] = commit
m["pf_source_commit"] = commit
p.write_text(json.dumps(m, indent=2) + "\n", encoding="utf-8")
PY
fi

promote() {
  local dest="$1"
  mkdir -p "${dest}"
  for f in science_claim_bundle.certified.json verification_result.json signed_science_claim_bundle.json; do
    cp -f "${RUN}/${f}" "${dest}/${f}"
  done
  if [[ -f "${MANIFEST}" ]]; then
    cp -f "${MANIFEST}" "${dest}/FIXTURE_MANIFEST.json"
  fi
  echo "promoted PF artifacts -> ${dest}"
}

promote "${PF_FIXTURES}"

PF_MANIFEST="${PF_FIXTURES}/FIXTURE_MANIFEST.json"
if [[ -f "${PF_MANIFEST}" ]]; then
  python3 - "${PF_MANIFEST}" "${PF_COMMIT}" <<'PY'
import json, pathlib, sys
p, commit = pathlib.Path(sys.argv[1]), sys.argv[2]
m = json.loads(p.read_text(encoding="utf-8"))
m["pf_source_commit"] = commit
m["regenerate"] = "make freeze-pcs-labtrust-release"
p.write_text(json.dumps(m, indent=2) + "\n", encoding="utf-8")
PY
fi

if [[ -d "${PCS_CORE_RELEASE}" ]]; then
  cp -f "${RUN}/verification_result.json" "${PCS_CORE_RELEASE}/"
  cp -f "${RUN}/signed_science_claim_bundle.json" "${PCS_CORE_RELEASE}/"
  cp -f "${RUN}/science_claim_bundle.certified.json" "${PCS_CORE_RELEASE}/"
  python3 "${ROOT}/scripts/pcs-sync-pcs-core-release.py" "${RUN}" "${PCS_CORE_RELEASE}" "${PF_COMMIT}"
fi

python3 "${ROOT}/scripts/pcs-freeze-labtrust-release-invalid.py" "${PF_FIXTURES}"

echo "OK: atomic promote from ${RUN}"
