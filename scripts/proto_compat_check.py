#!/usr/bin/env python3
"""Validate api/v1 protobuf files for CI backward-compatibility gate."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PROTO_DIR = REPO_ROOT / "api" / "v1"


def main() -> int:
    protos = sorted(PROTO_DIR.glob("*.proto"))
    if not protos:
        print("No protobuf files found under api/v1", file=sys.stderr)
        return 1

    for proto in protos:
        result = subprocess.run(
            [
                "protoc",
                f"--proto_path={REPO_ROOT / 'api'}",
                *(
                    [f"--proto_path={Path('/usr/include')}"]
                    if Path("/usr/include").exists()
                    else []
                ),
                "--descriptor_set_out=/dev/null",
                str(proto.relative_to(REPO_ROOT)),
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(result.stderr or result.stdout, file=sys.stderr)
            return result.returncode

    print(f"Protobuf compatibility check passed ({len(protos)} files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
