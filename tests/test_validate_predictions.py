# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Unit tests for validate_predictions (good/empty/pfmeta/diff/run_status).

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from experiments.scripts.validate_predictions import validate
from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_validate_good_predictions_pass():
    root = make_fake_runpair(instance_ids=["a", "b"])
    try:
        pred_path = root / "baseline" / "predictions.jsonl"
        ok, _ = validate(pred_path, expected_count=2, instance_ids_file=None, check_pfmeta=False, require_non_empty_diff=True)
        assert ok is True
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_validate_empty_file_fails():
    td = Path(tempfile.mkdtemp())
    try:
        pred = td / "p.jsonl"
        pred.write_text("", encoding="utf-8")
        ok, _ = validate(pred, expected_count=1, instance_ids_file=None, check_pfmeta=False, require_non_empty_diff=True)
        assert ok is False
    finally:
        shutil.rmtree(td, ignore_errors=True)


def test_validate_pfmeta_mismatch_fails():
    root = make_fake_runpair(instance_ids=["a", "b"])
    try:
        pred_path = root / "baseline" / "predictions.jsonl"
        pfmeta_path = pred_path.parent / (pred_path.stem + ".pfmeta.jsonl")
        pfmeta_path.write_text(json.dumps({"instance_id": "a"}) + "\n", encoding="utf-8")
        ok, _ = validate(pred_path, expected_count=2, instance_ids_file=None, check_pfmeta=True, require_non_empty_diff=True)
        assert ok is False
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_validate_not_diff_fails_without_allow_empty():
    td = Path(tempfile.mkdtemp())
    try:
        pred = td / "p.jsonl"
        pred.write_text(json.dumps({"instance_id": "x", "model_patch": "not a diff", "model_name_or_path": "m"}) + "\n", encoding="utf-8")
        ok, _ = validate(pred, expected_count=1, instance_ids_file=None, check_pfmeta=False, require_non_empty_diff=True)
        assert ok is False
    finally:
        shutil.rmtree(td, ignore_errors=True)


def test_validate_not_diff_passes_with_allow_empty():
    td = Path(tempfile.mkdtemp())
    try:
        pred = td / "p.jsonl"
        pred.write_text(json.dumps({"instance_id": "x", "model_patch": "not a diff", "model_name_or_path": "m"}) + "\n", encoding="utf-8")
        ok, _ = validate(pred, expected_count=1, instance_ids_file=None, check_pfmeta=False, require_non_empty_diff=False)
        assert ok is True
    finally:
        shutil.rmtree(td, ignore_errors=True)


def test_validate_run_status_partial_fails_without_allow_partial():
    root = make_fake_runpair(instance_ids=["a"])
    try:
        pred_dir = root / "baseline"
        (pred_dir / "run_status.json").write_text(json.dumps({"run_id": "r1", "status": "partial", "instances_planned": 5, "instances_written": 2, "first_error": "killed", "created_at": "2025-01-01T00:00:00Z"}, indent=2), encoding="utf-8")
        script = REPO_ROOT / "experiments" / "scripts" / "validate_predictions.py"
        proc = subprocess.run([sys.executable, str(script), str(pred_dir / "predictions.jsonl"), "-n", "1"], cwd=str(REPO_ROOT), capture_output=True, text=True)
        assert proc.returncode != 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_validate_run_status_partial_passes_with_allow_partial():
    root = make_fake_runpair(instance_ids=["a"])
    try:
        pred_dir = root / "baseline"
        (pred_dir / "run_status.json").write_text(json.dumps({"run_id": "r1", "status": "partial", "instances_planned": 5, "instances_written": 3, "first_error": None, "created_at": "2025-01-01T00:00:00Z"}, indent=2), encoding="utf-8")
        script = REPO_ROOT / "experiments" / "scripts" / "validate_predictions.py"
        proc = subprocess.run([sys.executable, str(script), str(pred_dir / "predictions.jsonl"), "-n", "1", "--allow-partial"], cwd=str(REPO_ROOT), capture_output=True, text=True)
        assert proc.returncode == 0
    finally:
        shutil.rmtree(root, ignore_errors=True)
