# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Load policy packs by name and compute canonical hash for evidence.

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

try:
    import yaml
except ImportError:
    yaml = None

# Pack name -> filename (without path)
PACK_FILES = {
    "swebench_safe_v1": "swebench_safe_v1.yaml",
}


def _policy_dir() -> Path:
    return Path(__file__).resolve().parent


def _canonical_dumps(obj: Any) -> str:
    """Deterministic JSON for hashing (sorted keys, no trailing whitespace)."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"))


def policy_hash(content: Dict[str, Any]) -> str:
    """Return SHA256 hex digest of canonical policy content."""
    return hashlib.sha256(_canonical_dumps(content).encode("utf-8")).hexdigest()


def load_pack(name: str, packs_dir: Optional[Path] = None) -> Tuple[Dict[str, Any], str]:
    """
    Load a policy pack by name. Returns (content_dict, sha256_hex).
    name: e.g. 'swebench_safe_v1' (without .yaml).
    Raises FileNotFoundError or ValueError if not found / invalid.
    """
    if yaml is None:
        raise RuntimeError("PyYAML is required for policy packs. Install with: pip install pyyaml")
    filename = PACK_FILES.get(name)
    if not filename:
        raise ValueError(f"Unknown policy pack: {name}. Known: {list(PACK_FILES)}")
    base = packs_dir or (_policy_dir() / "packs")
    path = base / filename
    if not path.exists():
        raise FileNotFoundError(f"Policy pack not found: {path}")
    raw = path.read_text(encoding="utf-8")
    content = yaml.safe_load(raw)
    if not isinstance(content, dict):
        raise ValueError(f"Policy pack must be a YAML object: {path}")
    h = policy_hash(content)
    return content, h
