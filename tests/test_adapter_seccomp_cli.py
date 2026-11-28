#!/usr/bin/env python3
"""Smoke-test actual seccomp-enabled adapter binaries on Linux x86_64."""
import http.server
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "target" / "debug"
PAYLOAD = b"adapter seccomp integration fixture"


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", str(len(PAYLOAD)))
        self.end_headers()
        self.wfile.write(PAYLOAD)


class AdapterSeccompCLI(unittest.TestCase):
    def test_file_read(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as directory:
            path = Path(directory) / "fixture.txt"
            path.write_bytes(PAYLOAD)
            result = subprocess.run(
                [str(TARGET / "fileread-adapter"), str(path)],
                text=True, capture_output=True, timeout=30,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(PAYLOAD.decode(), result.stdout)
            self.assertEqual(path.read_bytes(), PAYLOAD)

    def test_http_get(self):
        with http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler) as server:
            worker = threading.Thread(target=server.serve_forever, daemon=True)
            worker.start()
            try:
                env = {k: v for k, v in os.environ.items()
                       if not k.lower().endswith("_proxy")}
                env["NO_PROXY"] = "127.0.0.1,localhost"
                # Exercise both direct IPv4 and hostname resolution.
                for host in ("127.0.0.1", "localhost"):
                    with self.subTest(host=host):
                        result = subprocess.run(
                            [str(TARGET / "httpget-adapter"),
                             f"http://{host}:{server.server_port}/"],
                            env=env, text=True, capture_output=True, timeout=40,
                        )
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertIn("Status: 200", result.stdout)
                        self.assertIn(PAYLOAD.decode(), result.stdout)
            finally:
                server.shutdown()
                worker.join(timeout=5)


if __name__ == "__main__":
    unittest.main(verbosity=2)
