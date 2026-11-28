#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Compatibility entrypoint for the isolated native KMS/Vault signing fixture.

The former simulated encryption, signing and rotation checks did not exercise
the proxy or a cryptographic provider. This entrypoint executes the canonical
fixture with its existing isolated Linux CI prerequisites. Missing prerequisites
fail the invocation. Hardware attestation and production issuer provisioning
are outside the fixture's scope.
"""

from pathlib import Path
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    subprocess.run(
        [sys.executable, str(root / "scripts" / "test_kms_live_vault.py")],
        cwd=root,
        check=True,
    )


if __name__ == "__main__":
    main()
