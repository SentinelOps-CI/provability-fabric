#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Runtime evidence binding tests."""

from __future__ import annotations

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
BINDING = REPO / "examples" / "runtime-evidence-basic" / "binding-event.json"


def test_binding_event_shape() -> None:
    data = json.loads(BINDING.read_text(encoding="utf-8"))
    assert data["event_type"] == "evidence_v01_binding"
    assert "artifact_digests" in data
