"""Delegate `pf core <command>` to pf-core-validator."""

from __future__ import annotations

import sys

from pf_core.cli import main as pf_core_main


def main() -> None:
    """Entry point: expects argv like `core compile-observation ...`."""
    pf_core_main(sys.argv[1:])


if __name__ == "__main__":
    main()
