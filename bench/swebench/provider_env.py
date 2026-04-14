# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Single module for OpenHands LLM provider normalization, credentials, and model IDs.
# Used by engines/openhands_engine.py, runner.py env.json, and ensure_openhands_config.py.

from __future__ import annotations

import os
from typing import Any, Mapping, Optional

try:
    from constants import DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL
except ImportError:
    try:
        from bench.swebench.constants import DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL
    except ImportError:
        DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL = "https://api.pinference.ai/api/v1"  # type: ignore[misc]


def sanitize_env_value(val: Optional[str]) -> str:
    """Strip CR/LF, whitespace, and optional surrounding quotes (Windows .env friendly)."""
    if not val:
        return ""
    s = val.replace("\r", "").replace("\n", "").strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in ("'", '"'):
        s = s[1:-1]
    return s.strip()


def normalize_openhands_provider(environ: Optional[Mapping[str, str]] = None) -> str:
    """Normalize OPENHANDS_PROVIDER to openai | anthropic | prime_intellect."""
    env = environ if environ is not None else os.environ
    p = (env.get("OPENHANDS_PROVIDER") or "openai").strip().lower().replace("-", "_")
    if p in ("prime", "primeintellect"):
        return "prime_intellect"
    return p if p in ("openai", "anthropic", "prime_intellect") else "openai"


def llm_credentials(environ: Optional[Mapping[str, str]] = None) -> tuple[str, str, str]:
    """
    Return (api_key, base_url, provider_label) for [llm] config and LLM_* env.

    For prime_intellect, base_url is never empty: defaults to Prime Inference when unset.
    """
    env = environ if environ is not None else os.environ

    def sk(k: str) -> str:
        return sanitize_env_value(env.get(k))

    prov = normalize_openhands_provider(env)
    if prov == "anthropic":
        return sk("ANTHROPIC_API_KEY"), sk("ANTHROPIC_BASE_URL"), prov
    if prov == "prime_intellect":
        key = sk("PRIME_INTELLECT_API_KEY")
        base = sk("PRIME_INTELLECT_BASE_URL") or sk("OPENAI_BASE_URL")
        if not base:
            base = DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL
        return key, base, prov
    return sk("OPENAI_API_KEY"), sk("OPENAI_BASE_URL"), "openai"


def effective_llm_model(provider: str, model_name: str) -> str:
    """
    Normalize model IDs for Prime Inference (OpenAI-compatible API, vendor-qualified ids).

    Prime serves ids like ``google/gemini-2.5-flash``, ``meta-llama/llama-3.3-70b-instruct``,
    ``openai/gpt-4o-mini`` — not ``openai/google/...`` (that shape is rejected as unknown).
    """
    model = (model_name or "").strip()
    if not model:
        return model
    if provider != "prime_intellect":
        return model

    # Collapse mistaken double ``openai/`` prefix from some LiteLLM configs.
    while model.startswith("openai/openai/"):
        model = model[len("openai/") :]

    vendor_prefixes = (
        "anthropic/",
        "google/",
        "meta-llama/",
        "deepseek/",
        "qwen/",
        "mistralai/",
    )
    if model.startswith(vendor_prefixes):
        return model

    if model.startswith("openai/"):
        inner = model[len("openai/") :]
        if inner.startswith(vendor_prefixes):
            return inner
        if "/" not in inner:
            return model
        return model

    if "/" not in model:
        return "openai/" + model

    return model


def openhands_litellm_model(provider: str, model_name: str) -> str:
    """
    Model string for OpenHands + LiteLLM and for ``direct_agent`` HTTP to Prime Inference.

    LiteLLM rejects bare vendor ids like ``google/gemini-2.5-flash`` when using an OpenAI-compatible
    base URL (``LLM Provider NOT provided``). Prefix with ``openai/`` so routing uses the OpenAI
    adapter; the PF strict-compat proxy still forwards to Prime Inference.

    :func:`effective_llm_model` remains the vendor-normalized id (no ``openai/`` prefix on
    ``google/...``); use this function for any client that shares the same OpenAI-compatible
    entrypoint as OpenHands.
    """
    api = effective_llm_model(provider, model_name)
    if provider != "prime_intellect":
        return api
    vendor_prefixes = (
        "anthropic/",
        "google/",
        "meta-llama/",
        "deepseek/",
        "qwen/",
        "mistralai/",
    )
    if api.startswith(vendor_prefixes):
        return "openai/" + api
    return api


def resolve_openhands_model(
    configured_model: Optional[str] = None,
    environ: Optional[Mapping[str, str]] = None,
) -> str:
    """
    Resolve the raw model id used for OpenHands execution.

    Precedence:
    1) OPENHANDS_MODEL from environment (if non-empty)
    2) configured_model (runner/config argument)
    """
    env = environ if environ is not None else os.environ
    env_model = sanitize_env_value(env.get("OPENHANDS_MODEL"))
    if env_model:
        return env_model
    return (configured_model or "").strip()


def prime_team_id(environ: Optional[Mapping[str, str]] = None) -> str:
    env = environ if environ is not None else os.environ
    return (env.get("PRIME_TEAM_ID") or "").strip()


def provider_has_api_key(environ: Optional[Mapping[str, str]] = None) -> bool:
    """True if the active provider's primary API key env var is non-empty."""
    env = environ if environ is not None else os.environ
    prov = normalize_openhands_provider(env)
    if prov == "anthropic":
        return bool(sanitize_env_value(env.get("ANTHROPIC_API_KEY")))
    if prov == "prime_intellect":
        return bool(sanitize_env_value(env.get("PRIME_INTELLECT_API_KEY")))
    return bool(sanitize_env_value(env.get("OPENAI_API_KEY")))


def llm_env_diagnostics(environ: Optional[Mapping[str, str]] = None) -> dict[str, Any]:
    """
    Subset of fields for run env.json (no secrets): provider, base URL source, effective URL.
    """
    env = environ if environ is not None else os.environ
    prov = normalize_openhands_provider(env)
    _key, effective_base, _p = llm_credentials(env)
    pi_base = sanitize_env_value(env.get("PRIME_INTELLECT_BASE_URL"))
    oai_base = sanitize_env_value(env.get("OPENAI_BASE_URL"))
    out: dict[str, Any] = {
        "openhands_provider": prov,
        "prime_team_id_set": bool(prime_team_id(env)),
    }
    if prov == "prime_intellect":
        if pi_base:
            out["llm_base_url_source"] = "PRIME_INTELLECT_BASE_URL"
        elif oai_base:
            out["llm_base_url_source"] = "OPENAI_BASE_URL"
        else:
            out["llm_base_url_source"] = "DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL"
        out["llm_base_url_effective"] = effective_base
    elif oai_base:
        out["llm_base_url_source"] = "OPENAI_BASE_URL"
        out["llm_base_url_effective"] = oai_base
    else:
        out["llm_base_url_source"] = None
        out["llm_base_url_effective"] = None
    return out


def openhands_preflight_log_line(environ: Optional[Mapping[str, str]] = None) -> str:
    """Human-readable line for runner pre-instance loop (provider-aware)."""
    env = environ if environ is not None else os.environ
    prov = normalize_openhands_provider(env)
    ok = provider_has_api_key(env)
    if not ok:
        if prov == "prime_intellect":
            hint = "set PRIME_INTELLECT_API_KEY"
        elif prov == "anthropic":
            hint = "set ANTHROPIC_API_KEY"
        else:
            hint = "set OPENAI_API_KEY"
        return "OpenHands: LLM_API_KEY will be set from env: NO (%s)" % hint
    return "OpenHands: LLM_API_KEY will be set from env: yes (provider=%s)" % prov
