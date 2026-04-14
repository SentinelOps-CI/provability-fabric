# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Indicative USD estimates from token counts (public list prices; not billing truth).

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

# USD per 1M tokens (input, output) — update pricing_version when changing table
PRICING_VERSION = "2026-02-12"
# List every model id you run; figures are indicative public list prices only.
USD_PER_1M: dict[str, tuple[float, float]] = {
    "gpt-4o-mini": (0.15, 0.60),
    "gpt-4o": (2.50, 10.00),
    "gpt-4.1": (2.00, 8.00),
    "gpt-4.1-mini": (0.40, 1.60),
    "gpt-4-turbo": (10.00, 30.00),
    "gpt-3.5-turbo": (0.50, 1.50),
    "o3-mini": (1.10, 4.40),
    "o1-mini": (3.00, 12.00),
    "claude-3-5-sonnet": (3.00, 15.00),
    "claude-3-5-haiku": (0.80, 4.00),
    "claude-3-opus": (15.00, 75.00),
    "deepseek-chat": (0.14, 0.28),
    "deepseek-coder": (0.14, 0.28),
}


def resolve_model_key(model_name: str) -> str | None:
    if not model_name or not str(model_name).strip():
        return None
    m = str(model_name).strip().lower().replace("_", "-")
    # OpenAI-compatible stacks may emit duplicated path prefixes (e.g. Prime proxy: openai/openai/gpt-4o).
    while m.startswith("openai/openai/"):
        m = m[len("openai/") :]
    while m.startswith("anthropic/anthropic/"):
        m = m[len("anthropic/") :]
    # Longer keys first so gpt-4.1-mini beats gpt-4.1
    for key in sorted(USD_PER_1M.keys(), key=len, reverse=True):
        k = key.replace("_", "-")
        if k in m or m == k:
            return key
    if "haiku" in m and "claude" in m:
        return "claude-3-5-haiku"
    if "deepseek" in m and "coder" in m:
        return "deepseek-coder"
    if "deepseek" in m:
        return "deepseek-chat"
    if "o3-mini" in m or "o3mini" in m:
        return "o3-mini"
    if "o1-mini" in m or "o1mini" in m:
        return "o1-mini"
    if "mini" in m and "gpt-4o" in m:
        return "gpt-4o-mini"
    if "gpt-4o" in m and "mini" not in m:
        return "gpt-4o"
    return None


def tokens_to_usd(prompt_tokens: int, completion_tokens: int, model_key: str) -> float:
    inp, out = USD_PER_1M[model_key]
    return (prompt_tokens / 1_000_000.0) * inp + (completion_tokens / 1_000_000.0) * out


def _sum_tokens_and_model(run_dir: Path | None) -> tuple[int, int, str]:
    if not run_dir or not run_dir.exists():
        return 0, 0, ""
    p = run_dir / "summary.json"
    if not p.exists():
        return 0, 0, ""
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return 0, 0, ""
    pt = ct = 0
    model = ""
    for rec in data.get("instances") or []:
        pt += int(rec.get("prompt_tokens") or 0)
        ct += int(rec.get("completion_tokens") or 0)
        if not model and (rec.get("model_name") or "").strip():
            model = str(rec.get("model_name")).strip()
    return pt, ct, model


def pricing_errors_for_block(estimated: dict[str, Any] | None) -> list[str]:
    """Non-empty when baseline or PF has token totals but no USD pricing_key (strict gate)."""
    if not estimated or not isinstance(estimated, dict):
        return []
    out: list[str] = []
    for side in ("baseline", "pf"):
        b = estimated.get(side)
        if not isinstance(b, dict):
            continue
        pt = int(b.get("prompt_tokens_total") or 0)
        ct = int(b.get("completion_tokens_total") or 0)
        if pt + ct == 0:
            continue
        if b.get("pricing_key") is None:
            mn = b.get("model_name") or "(unknown)"
            out.append(
                "%s: model %r not in model_pricing USD_PER_1M; extend resolve_model_key or add entry"
                % (side, mn)
            )
    return out


def build_estimated_cost_usd_block(
    baseline_run_dir: Path | None,
    pf_run_dir: Path | None,
) -> dict[str, Any] | None:
    b_pt, b_ct, b_model = _sum_tokens_and_model(baseline_run_dir)
    p_pt, p_ct, p_model = _sum_tokens_and_model(pf_run_dir)
    if b_pt + b_ct + p_pt + p_ct == 0:
        return {
            "pricing_version": PRICING_VERSION,
            "disclaimer": "Indicative only; provider billing may differ. No token data found.",
            "baseline": None,
            "pf": None,
        }

    def side_block(pt: int, ct: int, model: str) -> dict[str, Any]:
        key = resolve_model_key(model)
        if not key:
            return {
                "prompt_tokens_total": pt,
                "completion_tokens_total": ct,
                "model_name": model or None,
                "total_usd": None,
                "pricing_key": None,
                "note": "Model not in pricing table; add to model_pricing.py USD_PER_1M",
            }
        return {
            "prompt_tokens_total": pt,
            "completion_tokens_total": ct,
            "model_name": model or None,
            "pricing_key": key,
            "total_usd": round(tokens_to_usd(pt, ct, key), 6),
        }

    return {
        "pricing_version": PRICING_VERSION,
        "disclaimer": "Indicative only; provider billing may differ.",
        "baseline": side_block(b_pt, b_ct, b_model),
        "pf": side_block(p_pt, p_ct, p_model),
    }
