# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Dataset ingestion for SWE-bench: load via HuggingFace datasets and parse
# instance_id, repo, base_commit, and issue text fields (aligned with SWE-bench docs).

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, List, Optional, Set

# Dataset name to HuggingFace dataset ID (aligned with SWE-bench docs).
DATASET_IDS = {
    "Lite": "princeton-nlp/SWE-bench_Lite",
    "Verified": "princeton-nlp/SWE-bench_Verified",
    "Full": "princeton-nlp/SWE-bench",
}


@dataclass
class SWEbenchInstance:
    """Parsed SWE-bench instance: identity, repo state, and issue text."""

    instance_id: str
    repo: str
    base_commit: str
    problem_statement: str
    hints_text: str = ""
    version: str = ""
    environment_setup_commit: str = ""
    fail_to_pass: str = ""
    pass_to_pass: str = ""
    created_at: str = ""
    test_patch: str = ""
    patch: str = ""
    raw: dict = field(default_factory=dict, repr=False)

    def to_dict(self) -> dict:
        return {
            "instance_id": self.instance_id,
            "repo": self.repo,
            "base_commit": self.base_commit,
            "problem_statement": self.problem_statement,
            "hints_text": self.hints_text,
            "version": self.version,
            "environment_setup_commit": self.environment_setup_commit,
            "FAIL_TO_PASS": self.fail_to_pass,
            "PASS_TO_PASS": self.pass_to_pass,
            "created_at": self.created_at,
            "test_patch": self.test_patch,
            "patch": self.patch,
        }


def _parse_row(row: dict) -> SWEbenchInstance:
    """Build SWEbenchInstance from a dataset row (HF or file)."""
    raw = dict(row)
    instance_id = str(raw.get("instance_id", raw.get("id", "")))
    repo = str(raw.get("repo", ""))
    base_commit = str(raw.get("base_commit", ""))
    problem_statement = str(raw.get("problem_statement", ""))
    hints_text = str(raw.get("hints_text", "") or "")
    version = str(raw.get("version", "") or "")
    environment_setup_commit = str(raw.get("environment_setup_commit", "") or "")
    fail_to_pass = raw.get("FAIL_TO_PASS", raw.get("fail_to_pass", ""))
    pass_to_pass = raw.get("PASS_TO_PASS", raw.get("pass_to_pass", ""))
    if isinstance(fail_to_pass, list):
        fail_to_pass = json.dumps(fail_to_pass)
    if isinstance(pass_to_pass, list):
        pass_to_pass = json.dumps(pass_to_pass)
    fail_to_pass = str(fail_to_pass or "")
    pass_to_pass = str(pass_to_pass or "")
    created_at = str(raw.get("created_at", "") or "")
    test_patch = str(raw.get("test_patch", "") or "")
    patch = str(raw.get("patch", "") or "")

    return SWEbenchInstance(
        instance_id=instance_id,
        repo=repo,
        base_commit=base_commit,
        problem_statement=problem_statement,
        hints_text=hints_text,
        version=version,
        environment_setup_commit=environment_setup_commit,
        fail_to_pass=fail_to_pass,
        pass_to_pass=pass_to_pass,
        created_at=created_at,
        test_patch=test_patch,
        patch=patch,
        raw=raw,
    )


def load_dataset(
    dataset: str,
    split: str,
    instance_ids: Optional[List[str]] = None,
    max_instances: Optional[int] = None,
    cache_dir: Optional[str] = None,
) -> List[SWEbenchInstance]:
    """
    Load SWE-bench instances from HuggingFace datasets (same as SWE-bench docs).
    Returns parsed instances with instance_id, repo, base_commit, and issue text fields.
    cache_dir: optional path for HuggingFace dataset cache (speeds repeated runs).
    """
    try:
        from datasets import load_dataset as hf_load
    except ImportError:
        raise RuntimeError(
            "HuggingFace 'datasets' is required. Install with: pip install datasets"
        ) from None

    ds_id = DATASET_IDS.get(dataset)
    if not ds_id:
        raise ValueError(f"Unknown dataset: {dataset}. Choose from: {list(DATASET_IDS)}")

    id_set = set(instance_ids) if instance_ids else None

    def _collect(dataset_handle: Any) -> List[SWEbenchInstance]:
        out: List[SWEbenchInstance] = []
        for row in dataset_handle:
            rec = dict(row)
            iid = str(rec.get("instance_id", ""))
            if id_set is not None and iid not in id_set:
                continue
            out.append(_parse_row(rec))
            if max_instances is not None and len(out) >= max_instances:
                break
        return out

    if cache_dir:
        try:
            ds = hf_load(ds_id, split=split, cache_dir=cache_dir)
            return _collect(ds)
        except OSError:
            ds = hf_load(ds_id, split=split)
            return _collect(ds)
    ds = hf_load(ds_id, split=split)
    return _collect(ds)


def load_from_file(
    path: str | Path,
    instance_ids: Optional[List[str]] = None,
    max_instances: Optional[int] = None,
) -> List[SWEbenchInstance]:
    """
    Load instances from a local JSON or JSONL file.
    Each record should include instance_id, repo, base_commit, problem_statement (and optionally hints_text).
    """
    path = Path(path)
    content = path.read_text(encoding="utf-8").strip()
    if path.suffix.lower() == ".jsonl":
        rows = [json.loads(line) for line in content.splitlines() if line.strip()]
    else:
        data = json.loads(content)
        rows = data if isinstance(data, list) else list(data.values())

    id_set = set(instance_ids) if instance_ids else None
    out: List[SWEbenchInstance] = []
    for r in rows:
        if not isinstance(r, dict):
            continue
        iid = str(r.get("instance_id", r.get("id", "")))
        if id_set is not None and iid not in id_set:
            continue
        out.append(_parse_row(r))
        if max_instances is not None and len(out) >= max_instances:
            break
    return out
