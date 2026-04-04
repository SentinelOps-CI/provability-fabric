# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
_SWB = REPO_ROOT / "bench" / "swebench"


def _run_cred_snippet(**env_updates: str) -> tuple[str, str, str]:
    env = {k: v for k, v in os.environ.items()}
    env.update(env_updates)
    code = (
        "from engines.openhands_engine import _llm_credentials; "
        "k,b,p=_llm_credentials(); print(k+'|'+b+'|'+p)"
    )
    r = subprocess.run(
        [sys.executable, "-c", code],
        cwd=str(_SWB),
        capture_output=True,
        text=True,
        env=env,
    )
    assert r.returncode == 0, r.stderr
    parts = (r.stdout or "").strip().split("|", 2)
    assert len(parts) == 3
    return parts[0], parts[1], parts[2]


def test_llm_credentials_prime_intellect():
    k, b, p = _run_cred_snippet(
        OPENHANDS_PROVIDER="prime_intellect",
        PRIME_INTELLECT_API_KEY="k1",
        PRIME_INTELLECT_BASE_URL="https://api.example/v1",
        OPENAI_API_KEY="",
    )
    assert k == "k1"
    assert b == "https://api.example/v1"
    assert p == "prime_intellect"


def test_llm_credentials_prime_falls_back_openai_base_url():
    k, b, _p = _run_cred_snippet(
        OPENHANDS_PROVIDER="prime_intellect",
        PRIME_INTELLECT_API_KEY="k2",
        PRIME_INTELLECT_BASE_URL="",
        OPENAI_BASE_URL="https://openai-compat.example",
    )
    assert k == "k2"
    assert b == "https://openai-compat.example"


def test_llm_credentials_prime_default_pinference_when_no_base_url():
    """Without PRIME/OPENAI base URL, engine must not send pit_* keys to api.openai.com."""
    k, b, p = _run_cred_snippet(
        OPENHANDS_PROVIDER="prime_intellect",
        PRIME_INTELLECT_API_KEY="k3",
        PRIME_INTELLECT_BASE_URL="",
        OPENAI_BASE_URL="",
    )
    assert k == "k3"
    assert b == "https://api.pinference.ai/api/v1"
    assert p == "prime_intellect"


def test_llm_credentials_openai_default():
    k, b, p = _run_cred_snippet(
        OPENHANDS_PROVIDER="openai",
        OPENAI_API_KEY="sk-x",
        OPENAI_BASE_URL="",
    )
    assert k == "sk-x"
    assert b == ""
    assert p == "openai"


def _run_openhands_litellm_model(provider: str, model: str) -> str:
    env = {k: v for k, v in os.environ.items()}
    code = (
        "from bench.swebench.provider_env import openhands_litellm_model; "
        f"print(openhands_litellm_model('{provider}', '{model}'))"
    )
    r = subprocess.run(
        [sys.executable, "-c", code],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        env=env,
    )
    assert r.returncode == 0, r.stderr
    return (r.stdout or "").strip()


def test_openhands_litellm_model_prime_openai_single_segment_unchanged():
    out = _run_openhands_litellm_model("prime_intellect", "openai/gpt-4o")
    assert out == "openai/gpt-4o"


def test_openhands_litellm_model_prime_collapses_double_openai_prefix():
    out = _run_openhands_litellm_model("prime_intellect", "openai/openai/gpt-4o")
    assert out == "openai/gpt-4o"


def test_openhands_litellm_model_prime_prefixes_vendor_for_litellm():
    out = _run_openhands_litellm_model("prime_intellect", "google/gemini-2.5-flash")
    assert out == "openai/google/gemini-2.5-flash"


def test_openhands_litellm_model_non_prime_unchanged():
    out = _run_openhands_litellm_model("openai", "openai/gpt-4o")
    assert out == "openai/gpt-4o"


def test_normalize_openai_payload_adds_missing_tool_call_content():
    env = {k: v for k, v in os.environ.items()}
    code = (
        "import json; "
        "from engines.openhands_engine import _normalize_openai_payload_for_strict_servers as f; "
        "p={'messages':[{'role':'assistant','tool_calls':[{'id':'1','type':'function','function':{'name':'x','arguments':'{}'}}]}]}; "
        "n,_=f(p); print(json.dumps(n, sort_keys=True))"
    )
    r = subprocess.run(
        [sys.executable, "-c", code],
        cwd=str(_SWB),
        capture_output=True,
        text=True,
        env=env,
    )
    assert r.returncode == 0, r.stderr
    out = r.stdout.strip()
    assert '"content": ""' in out
