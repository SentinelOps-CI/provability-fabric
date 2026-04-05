#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Used by run-baseline-pf-cycle.sh: resolve effective OpenHands model and validate provider keys.

from __future__ import annotations

import json
import os
import sys
from pathlib import Path


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
