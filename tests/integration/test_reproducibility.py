"""Reproducibility smoke (F06)."""

import hashlib
from pathlib import Path


def test_cargo_lock_present():
    root = Path(__file__).resolve().parents[2]
    lock = root / "Cargo.lock"
    assert lock.is_file()
    digest = hashlib.sha256(lock.read_bytes()).hexdigest()
    assert len(digest) == 64


def test_evidence_schemas_versioned():
    root = Path(__file__).resolve().parents[2]
    v01 = root / "specs" / "evidence" / "v0.1"
    v02 = root / "specs" / "evidence" / "v0.2"
    assert v01.is_dir() and v02.is_dir()
