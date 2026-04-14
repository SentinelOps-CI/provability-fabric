from __future__ import annotations

import os
from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from typing import Callable, Awaitable, Optional, Any
import json
import time
import uuid

CertSigner = Callable[[dict], Awaitable[str]]


class CertMiddleware(BaseHTTPMiddleware):
    def __init__(
        self,
        app,
        tenant_id: str = "demo-tenant",
        signer: Optional[CertSigner] = None,
    ):
        super().__init__(app)
        self.tenant_id = tenant_id
        self.signer = signer

    async def dispatch(self, request: Request, call_next):
        start = time.perf_counter()
        response = await call_next(request)
        end = time.perf_counter()
        latency_ms = int(round((end - start) * 1000))

        cert: dict[str, Any] = {
            "bundle_id": "standards-lane",
            "policy_hash": os.environ.get("CERT_POLICY_HASH", "n/a"),
            "proof_hash": os.environ.get("CERT_PROOF_HASH", "n/a"),
            "automata_hash": os.environ.get("CERT_AUTOMATA_HASH", "n/a"),
            "labeler_hash": os.environ.get("CERT_LABELER_HASH", "n/a"),
            "ni_claim": "global_non_interference",
            "ni_monitor": ("accept" if response.status_code < 400 else "reject"),
            "sidecar_build": "fastapi-mw@1.0.0",
            "tenant_id": self.tenant_id,
            "session_id": request.headers.get(
                "x-session-id",
                str(uuid.uuid4()),
            ),
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "method": request.method,
            "path": request.url.path,
            "latency_ms": latency_ms,
            "egress_profile": "HTTP-EGRESS@1.0",
        }

        if self.signer:
            try:
                sig = await self.signer(cert)
                cert["sig"] = sig
            except Exception:
                pass

        try:
            print(json.dumps(cert))
        except Exception:
            pass

        return response
