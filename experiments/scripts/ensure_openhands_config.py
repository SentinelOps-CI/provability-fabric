#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Optional: ensure a minimal config.toml under OH_PERSISTENCE_DIR or ~/.openhands
# for headless mode. OPENHANDS_PROVIDER selects key/base_url (openai|anthropic|prime_intellect).

from __future__ import annotations

import os
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from bench.swebench.provider_env import (  # noqa: E402
    llm_credentials,
    normalize_openhands_provider,
    openhands_litellm_model,
)


def main() -> int:
    persistence_dir = Path(
        os.environ.get("OH_PERSISTENCE_DIR", "").strip() or os.path.expanduser("~/.openhands")
    )
    config_path = persistence_dir / "config.toml"
    if config_path.exists():
        return 0

    api_key, base_url, prov = llm_credentials()
    if not api_key:
        print(
            "API key not set for OPENHANDS_PROVIDER=%s. Set OPENAI_API_KEY, ANTHROPIC_API_KEY, "
            "or PRIME_INTELLECT_API_KEY; set OPENHANDS_MODEL."
            % normalize_openhands_provider(),
            file=sys.stderr,
        )
        return 1

    model_raw = (os.environ.get("OPENHANDS_MODEL") or "gpt-4o-mini").strip()
    model = openhands_litellm_model(prov, model_raw)

    persistence_dir.mkdir(parents=True, exist_ok=True)

    def escape_toml_string(s: str) -> str:
        return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r")

    lines = [
        "# Auto-generated for headless (provider=%s)" % prov,
        "[llm]",
        'api_key = "%s"' % escape_toml_string(api_key),
        'model = "%s"' % escape_toml_string(model),
    ]
    if base_url:
        lines.append('base_url = "%s"' % escape_toml_string(base_url))
    lines.append("")

    config_path.write_text("\n".join(lines), encoding="utf-8")
    try:
        config_path.chmod(0o600)
    except OSError:
        pass
    print("Created %s (minimal [llm] for provider=%s)" % (config_path, prov), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
