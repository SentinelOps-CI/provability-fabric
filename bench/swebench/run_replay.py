#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Entry point for pf bench swebench replay (invoked from repo root).

import sys
from pathlib import Path

# Ensure bench/swebench is on path when run from repo root
_here = Path(__file__).resolve().parent
if str(_here) not in sys.path:
    sys.path.insert(0, str(_here))

from replay.__main__ import main

if __name__ == "__main__":
    sys.exit(main())
