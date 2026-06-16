#!/usr/bin/env python3
"""Minimal mock PF API for k6 platform performance smoke tests."""

from __future__ import annotations

import json
import time
from http.server import BaseHTTPRequestHandler, HTTPServer


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args) -> None:  # noqa: A003
        return

    def _send_json(self, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-PF-Plan-ms", "10")
        self.send_header("X-PF-Retrieval-ms", "20")
        self.send_header("X-PF-Kernel-ms", "5")
        self.send_header("X-PF-Egress-ms", "8")
        self.send_header("X-PF-Total-ms", "50")
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self) -> None:  # noqa: N802
        length = int(self.headers.get("Content-Length", 0))
        if length:
            _ = self.rfile.read(length)
        if self.path in ("/validate", "/execute"):
            self._send_json({"status": "ok", "path": self.path})
        else:
            self.send_response(404)
            self.end_headers()


def main() -> None:
    server = HTTPServer(("127.0.0.1", 8080), Handler)
    print("mock PF server listening on :8080", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
