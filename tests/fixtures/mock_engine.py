# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Reusable helpers for SWE-bench engine tests (no OpenHands dependency).

from __future__ import annotations

from typing import Any


def make_instance_dict(
    instance_id: str = "org__repo-1",
    *,
    repo: str = "org/repo",
    base_commit: str = "abc123",
) -> dict[str, Any]:
    """Minimal `instance.raw`-shaped dict for `run_engine_for_instance` / loader tests."""
    return {
        "instance_id": instance_id,
        "repo": repo,
        "base_commit": base_commit,
    }
