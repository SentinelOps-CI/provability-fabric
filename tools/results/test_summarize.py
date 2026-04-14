#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Tests for tools/results/summarize.py (P4.1 proof: no literal placeholder in output)

import json
import subprocess
import sys
from pathlib import Path


def test_summarize_no_placeholder_in_output():
    """Output must not contain literal 'placeholder' in bundle_id, signature, replay_drift."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "results" / "summarize.py"
    if not script.exists():
        raise SystemExit("summarize.py not found")
    out = subprocess.run(
        [sys.executable, str(script)],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=10,
    )
    assert out.returncode == 0, (out.stderr or out.stdout)
    data = json.loads(out.stdout)
    assert "bundle_id" in data
    assert "signature" in data
    assert "replay_drift" in data
    assert "placeholder" not in str(data.get("bundle_id", "")), "bundle_id must not be placeholder"
    assert "placeholder" not in str(data.get("signature", "")), "signature must not be placeholder"
    assert "placeholder" not in str(data.get("replay_drift", "")), "replay_drift must not be placeholder"
