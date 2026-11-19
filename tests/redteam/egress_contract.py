"""Strict, dependency-free parser for the Rust egress-firewall HTTP response.

The parser validates transport-level evidence shape; it does not establish the
correctness of a policy decision, certificate signature, or noninterference.
"""

from __future__ import annotations

from typing import Any


def parse_egress_response(
    payload: Any, *, expected_tenant: str, expected_plan_id: str
) -> tuple[str, dict[str, Any], bool, bool]:
    """Return (text, certificate, blocked, pii_detected) for an actual service reply.

    Reject missing or type-inconsistent fields, and responses attributed to a
    different tenant or request.  This is a schema/attribution check only; the
    certificate's cryptographic validity is outside this harness's scope.
    """
    if not isinstance(payload, dict):
        raise ValueError("egress response must be a JSON object")

    text = payload.get("text")
    blocked = payload.get("blocked")
    certificate = payload.get("certificate")
    if not isinstance(text, str):
        raise ValueError("egress response is missing string text")
    if type(blocked) is not bool:
        raise ValueError("egress response is missing boolean blocked")
    if not isinstance(certificate, dict):
        raise ValueError("egress response is missing certificate object")
    if not isinstance(certificate.get("cert_id"), str) or not certificate["cert_id"]:
        raise ValueError("egress certificate is missing cert_id")
    if certificate.get("tenant") != expected_tenant:
        raise ValueError("egress certificate tenant mismatch")
    if certificate.get("plan_id") != expected_plan_id:
        raise ValueError("egress certificate plan_id mismatch")

    flags = certificate.get("detector_flags")
    if not isinstance(flags, dict) or type(flags.get("pii_detected")) is not bool:
        raise ValueError("egress certificate is missing boolean detector_flags.pii_detected")
    return text, certificate, blocked, flags["pii_detected"]
