# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from experiments.scripts.model_pricing import pricing_errors_for_block, resolve_model_key


def test_pricing_errors_empty_when_no_tokens():
    assert pricing_errors_for_block({"baseline": None, "pf": None}) == []


def test_pricing_errors_when_unknown_model():
    est = {
        "baseline": {
            "prompt_tokens_total": 100,
            "completion_tokens_total": 50,
            "model_name": "unknown-vendor/model-xyz",
            "pricing_key": None,
        },
        "pf": {"prompt_tokens_total": 0, "completion_tokens_total": 0},
    }
    errs = pricing_errors_for_block(est)
    assert len(errs) == 1
    assert "baseline" in errs[0]


def test_resolve_model_key_strips_doubled_openai_prefix():
    assert resolve_model_key("openai/openai/gpt-4o") == "gpt-4o"


def test_resolve_model_key_strips_doubled_anthropic_prefix():
    assert resolve_model_key("anthropic/anthropic/claude-3-5-sonnet") == "claude-3-5-sonnet"


def test_pricing_errors_ok_for_gpt4o():
    est = {
        "baseline": {
            "prompt_tokens_total": 1000,
            "completion_tokens_total": 500,
            "model_name": "gpt-4o",
            "pricing_key": "gpt-4o",
        },
        "pf": {
            "prompt_tokens_total": 1000,
            "completion_tokens_total": 500,
            "model_name": "gpt-4o",
            "pricing_key": "gpt-4o",
        },
    }
    assert pricing_errors_for_block(est) == []
