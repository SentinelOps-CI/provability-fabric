#!/usr/bin/env python3
import json
import subprocess as sp
import pathlib

root = pathlib.Path(__file__).resolve().parents[2]
out = {
    "commit": None,
    "bundle_id": None,
    "proof": None,
    "signature": None,
    "replay_drift": None,
}

# commit
try:
    out["commit"] = (
        sp.check_output(["git", "rev-parse", "--short", "HEAD"], cwd=root)
        .decode()
        .strip()
    )
except Exception:
    out["commit"] = "unknown"

# proof - check if Spec.olean was built
spec_olean = (
    root / "spec-templates" / "v1" / "proofs" / ".lake" / "build" / "lib" / "Spec.olean"
)
if spec_olean.exists():
    out["proof"] = "verified"
else:
    out["proof"] = "fail"

# bundle_id: from runs dir or CLI if available; otherwise n/a
bundle_id = "n/a"
runs_dir = root / "runs"
if runs_dir.exists():
    for run_path in sorted(runs_dir.iterdir(), reverse=True)[:1]:
        manifest_path = run_path / "manifest.json"
        if manifest_path.exists():
            try:
                m = json.loads(manifest_path.read_text())
                bundle_id = m.get("bundle_hash") or m.get("bundle_id") or bundle_id
            except Exception:
                pass
        break
out["bundle_id"] = bundle_id

# signature: from evidence or n/a
out["signature"] = "n/a"

# replay_drift: from replay output or n/a
out["replay_drift"] = "n/a"

print(json.dumps(out, indent=2))
