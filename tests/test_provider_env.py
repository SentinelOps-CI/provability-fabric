# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.provider_env import (  # noqa: E402
    effective_llm_model,
    llm_credentials,
    openhands_litellm_model,
    llm_env_diagnostics,
    normalize_openhands_provider,
    openhands_preflight_log_line,
    provider_has_api_key,
    resolve_openhands_model,
)


def test_provider_has_api_key_prime() -> None:
    env = {
        "OPENHANDS_PROVIDER": "prime_intellect",
        "PRIME_INTELLECT_API_KEY": "pit_x",
    }
    assert provider_has_api_key(env) is True
    line = openhands_preflight_log_line(env)
    assert "yes" in line.lower()
    assert "prime_intellect" in line


def test_provider_has_api_key_prime_missing() -> None:
    env = {"OPENHANDS_PROVIDER": "prime_intellect", "PRIME_INTELLECT_API_KEY": ""}
    assert provider_has_api_key(env) is False
    line = openhands_preflight_log_line(env)
    assert "NO" in line
    assert "PRIME_INTELLECT_API_KEY" in line


def test_llm_env_diagnostics_prime_default_base() -> None:
    env = {
        "OPENHANDS_PROVIDER": "prime_intellect",
        "PRIME_INTELLECT_API_KEY": "k",
        "PRIME_INTELLECT_BASE_URL": "",
        "OPENAI_BASE_URL": "",
    }
    d = llm_env_diagnostics(env)
    assert d["openhands_provider"] == "prime_intellect"
    assert d["llm_base_url_source"] == "DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL"
    assert "pinference" in (d.get("llm_base_url_effective") or "")


def test_normalize_openhands_provider_aliases() -> None:
    assert normalize_openhands_provider({"OPENHANDS_PROVIDER": "Prime"}) == "prime_intellect"
    assert normalize_openhands_provider({"OPENHANDS_PROVIDER": "prime-intellect"}) == "prime_intellect"


def test_llm_credentials_openai_explicit_base_with_prime_provider_is_still_prime() -> None:
    """OPENAI_BASE_URL with prime_intellect is used as override, not a mode switch."""
    env = {
        "OPENHANDS_PROVIDER": "prime_intellect",
        "PRIME_INTELLECT_API_KEY": "pit",
        "PRIME_INTELLECT_BASE_URL": "",
        "OPENAI_BASE_URL": "https://custom.example/v1",
    }
    _k, base, prov = llm_credentials(env)
    assert prov == "prime_intellect"
    assert base == "https://custom.example/v1"
    d = llm_env_diagnostics(env)
    assert d["llm_base_url_source"] == "OPENAI_BASE_URL"


def test_resolve_openhands_model_prefers_env_over_config() -> None:
    env = {"OPENHANDS_MODEL": "google/gemini-2.5-flash"}
    assert resolve_openhands_model("gpt-4o-mini", env) == "google/gemini-2.5-flash"


def test_effective_model_for_prime_preserves_meta_llama_vendor_id() -> None:
    env = {
        "OPENHANDS_PROVIDER": "prime_intellect",
        "OPENHANDS_MODEL": "meta-llama/llama-3.3-70b-instruct",
    }
    raw = resolve_openhands_model("gpt-4o-mini", env)
    prov = normalize_openhands_provider(env)
    assert effective_llm_model(prov, raw) == "meta-llama/llama-3.3-70b-instruct"


def test_effective_model_for_prime_google_gemini_id() -> None:
    prov = "prime_intellect"
    assert effective_llm_model(prov, "google/gemini-2.5-flash") == "google/gemini-2.5-flash"


def test_effective_model_for_prime_strips_openai_google_prefix() -> None:
    prov = "prime_intellect"
    assert (
        effective_llm_model(prov, "openai/google/gemini-2.5-flash") == "google/gemini-2.5-flash"
    )


def test_openhands_litellm_adds_openai_prefix_for_prime_vendor_models() -> None:
    prov = "prime_intellect"
    assert openhands_litellm_model(prov, "google/gemini-2.5-flash") == "openai/google/gemini-2.5-flash"
    assert (
        openhands_litellm_model(prov, "meta-llama/llama-3.3-70b-instruct")
        == "openai/meta-llama/llama-3.3-70b-instruct"
    )


def test_openhands_litellm_matches_effective_for_bare_gpt_on_prime() -> None:
    prov = "prime_intellect"
    assert openhands_litellm_model(prov, "gpt-4o-mini") == effective_llm_model(prov, "gpt-4o-mini")
