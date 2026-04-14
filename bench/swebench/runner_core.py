# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Programmatic entry for SWE-bench runs (validated RunConfig -> _execute_run).

from __future__ import annotations

from bench.swebench.run_config import RunConfig


def run_swebench(config: RunConfig) -> int:
    """
    Run the SWE-bench pipeline using a validated :class:`RunConfig`.

    This is the library-oriented entry point; the CLI uses :func:`runner.main`
    which parses arguments, builds ``RunConfig``, validates, then calls
    :func:`bench.swebench.runner._execute_run`.
    """
    from bench.swebench.runner import _execute_run

    return _execute_run(config)
