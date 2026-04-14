#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Used by run-baseline-pf-cycle.sh: resolve effective OpenHands model and validate provider keys.

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

# When OPENHANDS_MODEL is unset and the manifest still pins a bare OpenAI-style id, Prime Inference
# routes it as openai/<id>; that often yields weak JSON-tooling or bad patches. Prefer a
# vendor-qualified LiteLLM id unless the user set OPENHANDS_MODEL explicitly.
_PRIME_MANIFEST_FALLBACK_MODEL = (
    os.environ.get("PF_PRIME_MANIFEST_FALLBACK_MODEL") or "google/gemini-2.5-flash"
).strip()


def _is_prime_unqualified_openai_style_model(model_id: str) -> bool:
    """
    True if model_id looks like a legacy manifest default (OpenAI product name, no vendor prefix).
    Vendor-qualified ids (contain '/') are left to the user/manifest.
    """
    m = (model_id or "").strip()
    if not m or "/" in m:
        return False
    ml = m.lower()
    if ml.startswith("gpt-") or ml.startswith("chatgpt-"):
        return True
    if re.match(r"^o[0-9]", ml) or ml.startswith("o1") or ml.startswith("o3"):
        return True
    return False


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: resolve_cycle_llm.py <manifest.json>", file=sys.stderr)
        return 2
    manifest_path = Path(sys.argv[1])
    env_model = (os.environ.get("OPENHANDS_MODEL") or "").strip()
    manifest_id = ""
    if manifest_path.is_file():
        try:
            m = json.loads(manifest_path.read_text(encoding="utf-8"))
            manifest_id = str((m.get("model") or {}).get("id") or "").strip()
        except (json.JSONDecodeError, OSError):
            pass
    effective = env_model or manifest_id
    if not effective:
        print(
            "Error: No LLM model set. Set OPENHANDS_MODEL or manifest.model.id in %s"
            % manifest_path,
            file=sys.stderr,
        )
        return 1
    provider = (os.environ.get("OPENHANDS_PROVIDER") or "openai").strip().lower().replace("-", "_")
    if provider in ("primeintellect", "prime"):
        provider = "prime_intellect"

    if provider == "prime_intellect":
        if not env_model and _is_prime_unqualified_openai_style_model(manifest_id):
            print(
                "Warning: OPENHANDS_MODEL unset and manifest.model.id=%r is an unqualified OpenAI-style id; "
                "Prime routes it as openai/<id>, which often breaks direct_agent quality. "
                "Using PF_PRIME_MANIFEST_FALLBACK_MODEL=%r instead. "
                "Set OPENHANDS_MODEL explicitly to override."
                % (manifest_id, _PRIME_MANIFEST_FALLBACK_MODEL),
                file=sys.stderr,
            )
            effective = _PRIME_MANIFEST_FALLBACK_MODEL
        elif env_model and _is_prime_unqualified_openai_style_model(env_model):
            print(
                "Warning: OPENHANDS_MODEL=%r with Prime is unqualified (no vendor/ prefix). "
                "Prefer a Prime-supported id such as google/gemini-2.5-flash if you see empty patches "
                "or patch_apply_check failures."
                % (env_model,),
                file=sys.stderr,
            )

    errs: list[str] = []
    if provider == "openai":
        if not (os.environ.get("OPENAI_API_KEY") or "").strip():
            errs.append("OPENHANDS_PROVIDER=openai requires OPENAI_API_KEY")
    elif provider == "anthropic":
        if not (os.environ.get("ANTHROPIC_API_KEY") or "").strip():
            errs.append("OPENHANDS_PROVIDER=anthropic requires ANTHROPIC_API_KEY")
    elif provider == "prime_intellect":
        if not (os.environ.get("PRIME_INTELLECT_API_KEY") or "").strip():
            errs.append("OPENHANDS_PROVIDER=prime_intellect requires PRIME_INTELLECT_API_KEY")
    else:
        errs.append("OPENHANDS_PROVIDER must be openai, anthropic, or prime_intellect (got %r)" % provider)

    if errs:
        for e in errs:
            print("Error: %s" % e, file=sys.stderr)
        return 1

    print(effective)
    return 0


if __name__ == "__main__":
    sys.exit(main())
