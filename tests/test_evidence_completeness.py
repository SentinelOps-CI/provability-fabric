# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Evidence bundle file completeness (instance dir layout).

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.evidence_writer import EvidenceBundle, EvidenceWriter
from bench.swebench.util import sanitize_instance_id


def test_evidence_writer_bundle_writes_core_artifacts():
    with tempfile.TemporaryDirectory() as tmp:
        run_dir = Path(tmp) / "run"
        iid = "django__django-99999"
        w = EvidenceWriter(run_dir)
        w.write_bundle(
            EvidenceBundle(
                instance_id=iid,
                model_patch="diff --git a/x b/x\n",
                log_text="log",
                engine_trace_dict={"tool_calls": [], "prompts_sent": []},
                engine_mode="mock",
                engine_success=True,
                engine_error=None,
                policy_name="p",
                policy_hash="h",
            )
        )
        sid = sanitize_instance_id(iid)
        inst = run_dir / sid
        for name in ("run.log", "model.patch", "patch.diff", "metadata.json", "engine_trace.json"):
            assert (inst / name).is_file(), f"missing {name}"
        meta = json.loads((inst / "metadata.json").read_text(encoding="utf-8"))
        assert meta["instance_id"] == iid
        assert meta["engine_mode"] == "mock"
        assert meta["policy_name"] == "p"
