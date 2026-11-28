#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
PF="${PF:-$ROOT/core/cli/pf/pf}"
EXAMPLE="$ROOT/specs/evidence/v0.1/examples/valid"
BUNDLE="$EXAMPLE/basic-evidence-bundle.json"
if [[ ! -x "$PF" ]]; then
  (cd "$ROOT/core/cli/pf" && go build -o pf .)
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$PF" evidence validate "$BUNDLE" --strict --base-dir "$EXAMPLE" --report-out "$tmp/pass.json"
python - "$BUNDLE" "$tmp/tampered.json" "$tmp/pass.json" <<'PY'
import json, sys
from pathlib import Path
source, target, report = map(Path, sys.argv[1:])
observed = json.loads(report.read_text())
assert observed["status"] == "pass" and not observed["errors"], observed
bundle = json.loads(source.read_text())
digest = bundle["bundle_digest"]
assert digest.startswith("sha256:") and len(digest) == 71
bundle["bundle_digest"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
target.write_text(json.dumps(bundle), encoding="utf-8")
PY
if "$PF" evidence validate "$tmp/tampered.json" --strict --base-dir "$EXAMPLE" --report-out "$tmp/fail.json"; then
  echo "expected tamper validation failure" >&2
  exit 1
fi
python - "$tmp/fail.json" <<'PY'
import json, sys
from pathlib import Path
report = json.loads(Path(sys.argv[1]).read_text())
assert report["status"] == "fail", report
assert len(report["errors"]) == 1, report
assert report["errors"][0].startswith("bundle_digest mismatch:"), report
PY
echo "evidence-v0.1 tamper case OK (specific digest rejection)"
