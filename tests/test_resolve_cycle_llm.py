# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "experiments" / "scripts" / "resolve_cycle_llm.py"


def test_resolve_prints_model_from_manifest_when_env_empty():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
        json.dump({"model": {"id": "gpt-4o"}}, f)
        p = f.name
    try:
        env = {k: v for k, v in os.environ.items()}
        env.pop("OPENHANDS_MODEL", None)
        env["OPENHANDS_PROVIDER"] = "openai"
        env["OPENAI_API_KEY"] = "sk-test"
        r = subprocess.run(
            [sys.executable, str(SCRIPT), p],
            capture_output=True,
            text=True,
            env=env,
        )
        assert r.returncode == 0
        assert r.stdout.strip() == "gpt-4o"
    finally:
        Path(p).unlink(missing_ok=True)


def test_prime_intellect_remaps_manifest_gpt_when_openhands_model_unset():
    """Bare gpt-* manifest defaults are a poor fit for Prime; cycle should substitute a vendor id."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
        json.dump({"model": {"id": "gpt-4o"}}, f)
        p = f.name
    try:
        env = {k: v for k, v in os.environ.items()}
        env.pop("OPENHANDS_MODEL", None)
        env.pop("PF_PRIME_MANIFEST_FALLBACK_MODEL", None)
        env["OPENHANDS_PROVIDER"] = "prime_intellect"
        env["PRIME_INTELLECT_API_KEY"] = "pi-key"
        r = subprocess.run(
            [sys.executable, str(SCRIPT), p],
            capture_output=True,
            text=True,
            env=env,
        )
        assert r.returncode == 0
        assert r.stdout.strip() == "google/gemini-2.5-flash"
        assert "Warning" in (r.stderr or "")
        assert "OPENHANDS_MODEL unset" in (r.stderr or "")
    finally:
        Path(p).unlink(missing_ok=True)


def test_prime_intellect_keeps_vendor_qualified_manifest_when_env_unset():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
        json.dump({"model": {"id": "google/gemini-2.5-flash"}}, f)
        p = f.name
    try:
        env = {k: v for k, v in os.environ.items()}
        env.pop("OPENHANDS_MODEL", None)
        env["OPENHANDS_PROVIDER"] = "prime_intellect"
        env["PRIME_INTELLECT_API_KEY"] = "pi-key"
        r = subprocess.run(
            [sys.executable, str(SCRIPT), p],
            capture_output=True,
            text=True,
            env=env,
        )
        assert r.returncode == 0
        assert r.stdout.strip() == "google/gemini-2.5-flash"
        assert "OPENHANDS_MODEL unset" not in (r.stderr or "")
    finally:
        Path(p).unlink(missing_ok=True)


def test_prime_intellect_warns_but_keeps_explicit_bare_gpt_env():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
        json.dump({"model": {"id": "gpt-4o"}}, f)
        p = f.name
    try:
        env = {k: v for k, v in os.environ.items()}
        env["OPENHANDS_MODEL"] = "gpt-4o-mini"
        env["OPENHANDS_PROVIDER"] = "prime_intellect"
        env["PRIME_INTELLECT_API_KEY"] = "pi-key"
        r = subprocess.run(
            [sys.executable, str(SCRIPT), p],
            capture_output=True,
            text=True,
            env=env,
        )
        assert r.returncode == 0
        assert r.stdout.strip() == "gpt-4o-mini"
        assert "Warning" in (r.stderr or "")
        assert "unqualified" in (r.stderr or "").lower()
    finally:
        Path(p).unlink(missing_ok=True)


def test_prime_intellect_allows_key_only_without_base_url():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
        json.dump({"model": {"id": "meta-llama/Llama-3.1-8B-Instruct"}}, f)
        p = f.name
    try:
        env = {k: v for k, v in os.environ.items()}
        env.pop("OPENAI_BASE_URL", None)
        env.pop("PRIME_INTELLECT_BASE_URL", None)
        env["OPENHANDS_PROVIDER"] = "prime_intellect"
        env["PRIME_INTELLECT_API_KEY"] = "pi-key"
        env["OPENHANDS_MODEL"] = "m"
        r = subprocess.run(
            [sys.executable, str(SCRIPT), p],
            capture_output=True,
            text=True,
            env=env,
        )
        assert r.returncode == 0
        assert r.stdout.strip() == "m"
    finally:
        Path(p).unlink(missing_ok=True)
