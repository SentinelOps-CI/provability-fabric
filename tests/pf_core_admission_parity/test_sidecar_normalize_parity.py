"""Parity: native sidecar emitter vs reference normalize.py (Phase 7 PR-4)."""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, Mapping

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
PF_CORE_ROOT = Path(
    os.environ.get(
        "PF_CORE_REF",
        REPO_ROOT.parent / "provability-fabric-core",
    )
)
NORMALIZE_PATH = (
    PF_CORE_ROOT / "adapters" / "provability-fabric" / "mcp_sidecar" / "normalize.py"
)
FIXTURES = REPO_ROOT / "runtime" / "sidecar-watcher" / "tests" / "fixtures"
SIDECAR_DIR = REPO_ROOT / "runtime" / "sidecar-watcher"

PARITY_KEYS = (
    "schema_version",
    "trace_id",
    "event_id",
    "observation_id",
    "decision",
    "policy_ref",
    "evidence_ref",
    "runtime_ref",
    "timestamp",
    "previous_event_hash",
)


def _load_normalize():
    if not NORMALIZE_PATH.is_file():
        pytest.skip(f"reference normalize.py not found at {NORMALIZE_PATH}")
    spec = importlib.util.spec_from_file_location("pf_sidecar_normalize", NORMALIZE_PATH)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(PF_CORE_ROOT / "pf-core" / "validator"))
    spec.loader.exec_module(mod)
    return mod


def _native_observation(fixture_name: str) -> Dict[str, Any]:
    fixture = FIXTURES / fixture_name
    proc = subprocess.run(
        ["cargo", "run", "--quiet", "--bin", "emit_observation"],
        cwd=SIDECAR_DIR,
        input=fixture.read_text(encoding="utf-8"),
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
    return json.loads(proc.stdout)


def _parity_subset(obs: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {k: obs[k] for k in PARITY_KEYS if k in obs}
    principal = obs.get("principal", {})
    out["principal_id"] = principal.get("id")
    out["tenant_id"] = principal.get("tenant_id")
    out["roles"] = list(principal.get("roles", []))
    action = obs.get("action", {})
    cap = action.get("capability", {})
    out["capability_id"] = cap.get("id")
    effects = action.get("effects", [])
    out["effect_kind"] = effects[0].get("kind") if effects else None
    reads = action.get("reads", [])
    out["resource_uri"] = reads[0].get("uri") if reads else None
    return out


@pytest.fixture(scope="module")
def normalize_mod():
    return _load_normalize()


@pytest.mark.parametrize(
    "fixture_name",
    ["sidecar_audit_line.json", "sidecar_denied_audit_line.json"],
)
def test_native_emitter_matches_normalize(fixture_name: str, normalize_mod) -> None:
    line = json.loads((FIXTURES / fixture_name).read_text(encoding="utf-8"))
    expected = normalize_mod.normalize_sidecar_line(line)
    native = _native_observation(fixture_name)
    assert _parity_subset(native) == _parity_subset(expected)


def test_ambiguous_line_errors_in_both_paths(normalize_mod) -> None:
    line = json.loads(
        (FIXTURES / "sidecar_ambiguous_audit_line.json").read_text(encoding="utf-8")
    )
    with pytest.raises(ValueError, match="capability_hint"):
        normalize_mod.normalize_sidecar_line(line)
    proc = subprocess.run(
        ["cargo", "run", "--quiet", "--bin", "emit_observation"],
        cwd=SIDECAR_DIR,
        input=json.dumps(line),
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode != 0
    assert "capability_hint" in (proc.stderr or proc.stdout)


def test_compile_observation_on_native_allowed(normalize_mod) -> None:
    pf_validator = PF_CORE_ROOT / "pf-core" / "validator"
    schemas = PF_CORE_ROOT / "pf-core" / "schemas"
    if not pf_validator.is_dir():
        pytest.skip("provability-fabric-core pf-core validator not present")
    native = _native_observation("sidecar_audit_line.json")
    env = {**os.environ, "PYTHONPATH": str(pf_validator)}
    obs_path = FIXTURES / "_native_allowed_obs.json"
    obs_path.write_text(json.dumps(native, indent=2), encoding="utf-8")
    try:
        proc = subprocess.run(
            [
                sys.executable,
                "-m",
                "pf_core.cli",
                "core",
                "compile-observation",
                "--schemas",
                str(schemas),
                "--file",
                str(obs_path),
            ],
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        assert proc.returncode == 0, proc.stderr or proc.stdout
    finally:
        obs_path.unlink(missing_ok=True)
