#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Proof tests for P14 / F12: build-impacted path writes real artifacts.

import json
import subprocess
import sys
import tempfile
from pathlib import Path


def test_build_impacted_requires_output_dir():
    """--build-impacted without --output-dir exits non-zero."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    result = subprocess.run(
        [sys.executable, str(script), "--build-impacted"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=30,
    )
    assert result.returncode != 0
    assert "output-dir" in (result.stdout + result.stderr).lower()


def test_build_impacted_writes_plan():
    """--build-impacted emits build_plan.json and build_impacted.sh."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        result = subprocess.run(
            [
                sys.executable,
                str(script),
                "--build-impacted",
                "--output-dir",
                str(out),
                "--workspace",
                str(root),
            ],
            capture_output=True,
            text=True,
            cwd=root,
            timeout=120,
        )
        assert result.returncode == 0, result.stderr
        plan = out / "build_plan.json"
        shell = out / "build_impacted.sh"
        assert plan.is_file()
        assert shell.is_file()
        data = json.loads(plan.read_text(encoding="utf-8"))
        assert data["build_type"] == "impacted_only"
        assert "build_steps" in data


def test_impacted_only_help():
    """--help works."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=10,
    )
    assert result.returncode == 0
    assert "build-impacted" in result.stdout or "output-dir" in result.stdout


def test_rust_selector_matches_workspace_manifests():
    """Every path mapping must name the actual Cargo workspace package."""
    import runpy
    import tomllib

    root = Path(__file__).resolve().parents[2]
    selector = runpy.run_path(str(root / "tools" / "select_impacted_rust.py"))
    workspace = tomllib.loads((root / "Cargo.toml").read_text(encoding="utf-8"))
    expected = {}
    for member in workspace["workspace"]["members"]:
        manifest = tomllib.loads(
            (root / member / "Cargo.toml").read_text(encoding="utf-8")
        )
        expected[member.rstrip("/") + "/"] = manifest["package"]["name"]

    mappings = selector["PATH_TO_CRATE"]
    assert len(mappings) == len(expected)
    assert dict(mappings) == expected
    for prefix, package in expected.items():
        assert selector["crates_from_files"]([prefix + "Cargo.toml"]) == {package}


def test_rust_selector_routes_adapter_and_dsse_changes():
    """Targeted changes select real testable packages, not directory names."""
    import runpy

    root = Path(__file__).resolve().parents[2]
    selector = runpy.run_path(str(root / "tools" / "select_impacted_rust.py"))
    cases = {
        "adapters/http-get/src/lib.rs": "httpget-adapter",
        "adapters/file-read/src/lib.rs": "fileread-adapter",
        "core/crypto/dsse-rs/src/lib.rs": "pf-dsse",
    }
    for path, package in cases.items():
        result = selector["build_result"]([path], False)
        assert result["workspace_crates"] == [package]
        assert result["run_workspace_libs"] is True
        assert result["run_sidecar_curated"] is False
        assert result["full_workspace"] is False
