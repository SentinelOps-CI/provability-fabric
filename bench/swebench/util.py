# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Shared helpers for bench/swebench and experiment scripts (instance_id, paths).

from __future__ import annotations


def sanitize_instance_id(instance_id: str) -> str:
    """Sanitize instance_id for use as a filesystem directory name (alnum, hyphen, underscore)."""
    return "".join(c if c.isalnum() or c in "-_" else "_" for c in instance_id)
