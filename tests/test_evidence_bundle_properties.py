# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Property-based checks for evidence bundles (Hypothesis optional).

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.evidence_writer import EvidenceBundle, EvidenceWriter
from bench.swebench.util import sanitize_instance_id

pytest.importorskip("hypothesis")

from hypothesis import given
from hypothesis import strategies as st


@given(
    patch=st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=126), max_size=400),
    log=st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=126), max_size=200),
)
def test_evidence_roundtrip_metadata_patch_length_matches(patch: str, log: str):
    with tempfile.TemporaryDirectory() as tmp:
        run_dir = Path(tmp) / "r"
        w = EvidenceWriter(run_dir)
        w.write_bundle(
            EvidenceBundle(
                instance_id="org__repo-42",
                model_patch=patch,
                log_text=log,
                engine_trace_dict={"tool_calls": []},
                engine_mode="mock",
                engine_success=True,
            )
        )
        sid = sanitize_instance_id("org__repo-42")
        meta = json.loads((run_dir / sid / "metadata.json").read_text(encoding="utf-8"))
        assert meta["patch_length"] == len(patch)
