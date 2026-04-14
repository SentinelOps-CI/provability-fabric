# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.loader import load_from_file, SWEbenchInstance


def test_loader_from_jsonl_fixture():
    path = REPO_ROOT / "tests" / "fixtures" / "bench_swebench_instances.jsonl"
    instances = load_from_file(path)
    assert len(instances) == 3
    for inst in instances:
        assert isinstance(inst, SWEbenchInstance)
        assert inst.instance_id
        assert inst.repo
        assert inst.base_commit
        assert inst.problem_statement is not None
    assert instances[0].instance_id == "smoke-inst-1"
    assert instances[0].repo == "org/repo1"


def test_loader_max_instances():
    path = REPO_ROOT / "tests" / "fixtures" / "bench_swebench_instances.jsonl"
    instances = load_from_file(path, max_instances=2)
    assert len(instances) == 2


def test_loader_instance_ids_filter():
    path = REPO_ROOT / "tests" / "fixtures" / "bench_swebench_instances.jsonl"
    instances = load_from_file(path, instance_ids=["smoke-inst-2"])
    assert len(instances) == 1
    assert instances[0].instance_id == "smoke-inst-2"
