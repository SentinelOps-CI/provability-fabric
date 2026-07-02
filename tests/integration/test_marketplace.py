"""Marketplace smoke (F06)."""

import json
from pathlib import Path


def test_marketplace_ui_package():
    root = Path(__file__).resolve().parents[2]
    pkg_path = root / "marketplace" / "ui" / "package.json"
    data = json.loads(pkg_path.read_text(encoding="utf-8"))
    assert "scripts" in data
    assert "build" in data["scripts"]


def test_marketplace_api_go_module():
    root = Path(__file__).resolve().parents[2]
    assert (root / "marketplace" / "api" / "go.mod").is_file()
