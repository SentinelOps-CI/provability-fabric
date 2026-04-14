# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Patch / trace extraction helpers (runner internals used by OpenHands path).

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.runner import _openhands_trace_has_content


def test_openhands_trace_has_content_empty():
    assert _openhands_trace_has_content(None) is False
    assert _openhands_trace_has_content({}) is False
    assert _openhands_trace_has_content({"tool_calls": [], "files_modified": [], "raw_events": []}) is False


def test_openhands_trace_has_content_tool_calls():
    assert _openhands_trace_has_content({"tool_calls": [{"x": 1}], "files_modified": []}) is True


def test_openhands_trace_has_content_files_modified():
    assert _openhands_trace_has_content({"tool_calls": [], "files_modified": ["a.py"]}) is True


def test_openhands_trace_has_content_raw_events():
    assert _openhands_trace_has_content({"tool_calls": [], "files_modified": [], "raw_events": [{"k": 1}]}) is True
