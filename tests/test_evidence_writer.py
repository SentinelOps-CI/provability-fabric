# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.evidence_writer import EvidenceBundle, EvidenceWriter, write_instance_evidence
from bench.swebench.util import sanitize_instance_id


def test_write_instance_evidence_creates_expected_files():
    with tempfile.TemporaryDirectory() as tmp:
        run_dir = Path(tmp) / "run1"
        write_instance_evidence(
            run_dir,
            "django__django-1",
            "patch",
            "logline",
            engine_trace_dict={"tool_calls": []},
            policy_name="p",
            policy_hash="h",
            engine_mode="mock",
            engine_success=True,
            engine_error=None,
        )
        sid = sanitize_instance_id("django__django-1")
        inst = run_dir / sid
        assert (inst / "run.log").read_text(encoding="utf-8").startswith("logline")
        assert (inst / "model.patch").read_text(encoding="utf-8") == "patch"
        meta = json.loads((inst / "metadata.json").read_text(encoding="utf-8"))
        assert meta["instance_id"] == "django__django-1"
        assert meta["policy_name"] == "p"


def test_evidence_writer_write_bundle():
    with tempfile.TemporaryDirectory() as tmp:
        run_dir = Path(tmp) / "r"
        w = EvidenceWriter(run_dir)
        w.write_bundle(
            EvidenceBundle(
                instance_id="a__b-1",
                model_patch="x",
                log_text="y",
                engine_mode="mock",
                engine_success=True,
            )
        )
        sid = sanitize_instance_id("a__b-1")
        assert (run_dir / sid / "patch.diff").read_text(encoding="utf-8") == "x"


def test_evidence_writer_write_trace():
    with tempfile.TemporaryDirectory() as tmp:
        run_dir = Path(tmp) / "r"
        w = EvidenceWriter(run_dir)
        w.write_trace("x__y-1", {"tool_calls": [], "source": "test"})
        sid = sanitize_instance_id("x__y-1")
        meta = json.loads((run_dir / sid / "engine_trace.json").read_text(encoding="utf-8"))
        assert meta["source"] == "test"
