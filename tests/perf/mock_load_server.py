#!/usr/bin/env python3
"""Local mock endpoints for CI load / edge / ProofMeter smokes."""

from __future__ import annotations

import json
from http.server import BaseHTTPRequestHandler, HTTPServer


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args) -> None:  # noqa: A003
        return

    def _json(self, code: int, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Cache", "HIT" if self.path.startswith("/quote") else "MISS")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:  # noqa: N802
        if self.path.startswith("/health"):
            self._json(200, {"status": "ok"})
        elif self.path.startswith("/quote"):
            self._json(200, {"quote": 1.0, "cache": "ok"})
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self) -> None:  # noqa: N802
        length = int(self.headers.get("Content-Length", 0))
        if length:
            _ = self.rfile.read(length)
        if self.path in ("/proof", "/webhook/cache-invalidate", "/validate", "/execute"):
            self._json(200, {"status": "ok", "path": self.path})
        else:
            self.send_response(404)
            self.end_headers()


def main() -> None:
    import os

    port = int(os.environ.get("MOCK_LOAD_PORT", "8080"))
    host = os.environ.get("MOCK_LOAD_HOST", "127.0.0.1")
    server = HTTPServer((host, port), Handler)
    print(f"mock load server listening on {host}:{port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
