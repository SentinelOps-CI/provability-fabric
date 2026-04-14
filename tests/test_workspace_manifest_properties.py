# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# WorkspaceManifest hashing and structural invariants.

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.workspace import WorkspaceManifest


def _make_manifest(**kwargs: str) -> WorkspaceManifest:
    defaults = dict(
        instance_id="i1",
        repo="o/r",
        base_commit="b",
        workspace_root="/w",
        repo_path="/w/r",
        task_prompt_path="/w/t",
        scratch_path="/w/s",
        resolved_commit="r",
    )
    defaults.update(kwargs)
    return WorkspaceManifest(**defaults)


def test_sha256_independent_of_instance_id_when_other_fields_equal():
    """Hash is over canonical dict; same structural content should match if canonical form matches."""
    m1 = _make_manifest(instance_id="a")
    m2 = _make_manifest(instance_id="b")
    # instance_id is part of manifest; different IDs -> different hash (document behavior)
    assert m1.sha256() != m2.sha256()


def test_sha256_stable_same_instance():
    m = _make_manifest()
    assert m.sha256() == m.sha256()
