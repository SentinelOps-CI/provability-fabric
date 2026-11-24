#!/usr/bin/env python3
"""Exercise the real sandbox CLI with deterministic binary core Wasm controls."""

import argparse
import hashlib
import json
import pathlib
import subprocess
import tempfile
import unittest


def uleb(value):
    """Encode an unsigned integer in WebAssembly LEB128 format."""
    if value < 0:
        raise ValueError("unsigned integer required")
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def section(identifier, payload):
    return bytes([identifier]) + uleb(len(payload)) + payload


def name(value):
    encoded = value.encode("utf-8")
    return uleb(len(encoded)) + encoded


def module(body=b"\x01", *, imported=False, memory_pages=None, export=True):
    """Build a small module with a () -> () entrypoint and optional host import."""
    result = b"\x00asm\x01\x00\x00\x00"
    result += section(1, b"\x01\x60\x00\x00")  # One function type.
    if imported:
        result += section(2, b"\x01" + name("wasi_snapshot_preview1") + name("sock_open") + b"\x00\x00")
    result += section(3, b"\x01\x00")
    if memory_pages is not None:
        result += section(5, b"\x01\x00" + uleb(memory_pages))
    if export:
        result += section(7, b"\x01" + name("_start") + b"\x00" + uleb(int(imported)))
    code = b"\x00" + body + b"\x0b"  # Zero local declarations; end.
    result += section(10, b"\x01" + uleb(len(code)) + code)
    return result


class SandboxCLI(unittest.TestCase):
    executable = None
    image = None

    def invoke(self, wasm, *options):
        with tempfile.TemporaryDirectory(prefix="pf-wasm-cli-") as directory:
            root = pathlib.Path(directory)
            fixture = root / "guest.wasm"
            fixture.write_bytes(wasm)
            # TemporaryDirectory is private by default. The image uses a
            # non-root UID; only this generated public fixture needs access.
            root.chmod(0o755)
            fixture.chmod(0o644)
            if self.image:
                command = [
                    "docker", "run", "--rm", "--network", "none",
                    "--read-only", "--mount",
                    f"type=bind,source={root},target=/fixtures,readonly",
                    self.image, "--module", "/fixtures/guest.wasm",
                ]
            else:
                command = [str(self.executable), "--module", str(fixture)]
            return subprocess.run(
                [*command, *options], capture_output=True, text=True,
                timeout=30, check=False,
            )

    def assert_execution(self, process, *, success, fuel):
        self.assertEqual(process.returncode, 0 if success else 1, process.stderr)
        result = json.loads(process.stdout)
        self.assertIs(result["success"], success)
        self.assertIsNone(result["witness"])
        self.assertIsInstance(result["fuel_consumed"], int)
        self.assertGreaterEqual(result["fuel_consumed"], 0)
        self.assertLessEqual(result["fuel_consumed"], fuel)
        self.assertIsInstance(result["execution_time_ms"], int)
        self.assertGreaterEqual(result["execution_time_ms"], 0)
        if success:
            self.assertIsNone(result["error"])
            self.assertGreater(result["fuel_consumed"], 0)
        else:
            self.assertTrue(result["error"])
        return result

    def test_success_and_hash_binding(self):
        wasm = module()
        digest = hashlib.sha256(wasm).hexdigest()
        self.assert_execution(
            self.invoke(wasm, "--expected-hash", digest, "--fuel-limit", "1000"),
            success=True, fuel=1000,
        )
        rejected = self.invoke(wasm, "--expected-hash", "0" * 64)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn("SHA256 mismatch", rejected.stderr)

    def test_trap(self):
        self.assert_execution(
            self.invoke(module(b"\x00"), "--fuel-limit", "1000"),
            success=False, fuel=1000,
        )

    def test_fuel_exhaustion(self):
        # loop blocktype=empty; br depth=0; end
        result = self.assert_execution(
            self.invoke(module(b"\x03\x40\x0c\x00\x0b"), "--fuel-limit", "100"),
            success=False, fuel=100,
        )
        self.assertIn("fuel", result["error"].lower())

    def test_import_is_rejected(self):
        result = self.invoke(module(imported=True))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("guest imports are unsupported", result.stderr)

    def test_missing_entrypoint(self):
        result = self.assert_execution(
            self.invoke(module(export=False), "--fuel-limit", "1000"),
            success=False, fuel=1000,
        )
        self.assertIn("_start", result["error"])

    def test_initial_memory_limit(self):
        self.assert_execution(
            self.invoke(module(memory_pages=1025), "--fuel-limit", "1000"),
            success=False, fuel=1000,
        )

    def test_unsupported_options(self):
        for options, expected in [
            (["--allow-network"], "host network access is unsupported"),
            (["--allow-fs"], "host filesystem access is unsupported"),
            (["--input", "{}"], "guest input ABI is unsupported"),
            (["--fuel-limit", "0"], "fuel limit must be positive"),
        ]:
            with self.subTest(options=options):
                result = self.invoke(module(), *options)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--executable", type=pathlib.Path)
    target.add_argument("--docker-image")
    args = parser.parse_args()
    SandboxCLI.executable = args.executable.resolve() if args.executable else None
    SandboxCLI.image = args.docker_image
    unittest.main(argv=[__file__], verbosity=2)
