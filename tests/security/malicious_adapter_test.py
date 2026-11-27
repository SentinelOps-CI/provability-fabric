#!/usr/bin/env python3
"""Execute TRUST-FIRE Phase 3 against the real restricted sandbox CLI.

SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

This tests local sandbox behavior, not registry publication, syscall auditing,
or deployment-wide isolation. Missing tools and timeouts are failures.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SUITE = ROOT / "tests" / "test_wasm_sandbox_cli.py"
BUILD_TIMEOUT = 1200
TEST_TIMEOUT = 300


def build_sandbox(sandbox_path: Path) -> Path:
    """Resolve the actual executable from a successful locked Cargo build."""
    manifest = sandbox_path.resolve() / "Cargo.toml"
    if not manifest.is_file():
        raise FileNotFoundError(manifest)
    result = subprocess.run(
        ["cargo", "build", "--locked", "--manifest-path", str(manifest),
         "--package", "wasm-sandbox", "--message-format=json-render-diagnostics"],
        cwd=ROOT, capture_output=True, text=True, timeout=BUILD_TIMEOUT,
        check=False,
    )
    if result.stderr:
        print(result.stderr, file=sys.stderr, end="")
    if result.returncode:
        raise RuntimeError(f"Locked sandbox build failed ({result.returncode})")

    executables = set()
    for line in result.stdout.splitlines():
        message = json.loads(line)
        if message.get("reason") != "compiler-artifact":
            continue
        target = message.get("target", {})
        if (target.get("name") == "wasm-sandbox"
                and "bin" in target.get("kind", [])
                and message.get("executable")):
            executables.add(Path(message["executable"]).resolve())
    if len(executables) != 1:
        raise RuntimeError(f"Expected one sandbox executable, found {len(executables)}")
    executable = executables.pop()
    if not executable.is_file():
        raise FileNotFoundError(executable)
    return executable


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry-path", default="registry",
                        help="Legacy compatibility argument; registry is not tested")
    parser.add_argument("--wasm-sandbox-path", type=Path,
                        default=ROOT / "runtime" / "wasm-sandbox")
    parser.add_argument("--executable", type=Path,
                        help="Use an explicitly supplied, already-built sandbox")
    args = parser.parse_args()

    try:
        executable = (args.executable.resolve() if args.executable
                      else build_sandbox(args.wasm_sandbox_path))
        if not executable.is_file():
            raise FileNotFoundError(executable)
        print("TRUST-FIRE Phase 3: executing actual binary guest controls", flush=True)
        print("Registry publication and syscall logging are outside this test's scope.",
              flush=True)
        result = subprocess.run(
            [sys.executable, str(SUITE), "--executable", str(executable)],
            cwd=ROOT, timeout=TEST_TIMEOUT, check=False,
        )
        if result.returncode:
            print("TRUST-FIRE Phase 3 FAILED", file=sys.stderr)
            return 1
        print("TRUST-FIRE Phase 3 PASSED: executable sandbox controls")
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"TRUST-FIRE Phase 3 FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
