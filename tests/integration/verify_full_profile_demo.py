#!/usr/bin/env python3
"""Check live full-profile demo contracts using disposable synthetic inputs.

This probe intentionally expects proof refusal for generated Lean obligations
containing admissions. Passing does not establish deployed policy enforcement,
certificate provenance, replay, or fraud detection quality.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import ProxyHandler, Request, build_opener

GATEWAY = "http://127.0.0.1:8000"
DEMO = "http://127.0.0.1:3001"

# The public demo setup uses this policy. Compilation is deliberately allowed;
# generated obligations containing admitted theorems must be refused as proofs.
FRAUD_POLICY_ENGLISH = """
Only FraudService may call the score endpoint.

Alerts are emitted only after L_txn flows to L_ops via Δ_Risk declassification.

Rate limit alerts to 5 per 10 seconds per tenant.

Block transactions with fraud score greater than or equal to 0.93.

Allow read access to transaction data for users with reader role when tenant is verified.

Forbid write access to fraud scores for users without admin role.

Budget limit 1000 USD per day for fraud scoring operations.
"""

OPENER = build_opener(ProxyHandler({}))


def exchange(
    url: str, *, method: str = "GET", payload: dict[str, Any] | None = None
) -> tuple[int, bytes]:
    """Return the actual HTTP status and response, including HTTP errors."""
    body = json.dumps(payload).encode("utf-8") if payload is not None else None
    headers = {"Content-Type": "application/json"} if body is not None else {}
    request = Request(url, data=body, headers=headers, method=method)
    try:
        with OPENER.open(request, timeout=15) as response:
            return response.status, response.read()
    except HTTPError as error:
        return error.code, error.read()


def checked_json(
    url: str,
    *,
    expected: int = 200,
    method: str = "GET",
    payload: dict[str, Any] | None = None,
) -> Any:
    """Reject missing, unexpected, or malformed HTTP observations."""
    status, raw = exchange(url, method=method, payload=payload)
    if status != expected:
        raise AssertionError(
            f"{method} {url} returned HTTP {status}, expected {expected}: {raw[:240]!r}"
        )
    try:
        return json.loads(raw)
    except (ValueError, UnicodeDecodeError) as error:
        raise AssertionError(f"{method} {url} returned invalid JSON") from error


def verify_contracts() -> dict[str, Any]:
    """Check deployment health, proof refusal, and synthetic demo REST behavior."""
    gateway = checked_json(f"{GATEWAY}/health")
    assert isinstance(gateway, dict) and gateway.get("status") in {
        "healthy", "degraded"
    }, "API gateway did not report an expected health status"

    status, body = exchange(f"{DEMO}/health")
    assert status == 200 and body == b"ok", "Demo HTTP liveness failed"
    ready = checked_json(f"{DEMO}/ready")
    assert isinstance(ready, dict) and ready.get("ready") is True

    tools = checked_json(f"{DEMO}/api/tools")
    assert isinstance(tools, list), "Tool discovery must be an array"
    names = {tool.get("name") for tool in tools if isinstance(tool, dict)}
    assert {"ingest_transaction", "score_fraud", "get_transaction"} <= names

    policy = checked_json(
        f"{GATEWAY}/api/v1/policy/compile",
        method="POST",
        payload={
            "english": FRAUD_POLICY_ENGLISH,
            "policy_id": "ci-proof-refusal-fixture",
            "version": "1.0.0",
        },
    )
    assert isinstance(policy, dict), "Policy compilation returned invalid JSON"
    policy_hash = policy.get("policy_hash")
    action_dsl = policy.get("action_dsl", policy.get("actionDsl"))
    assert isinstance(policy_hash, str) and policy_hash, "Missing policy hash"
    assert isinstance(action_dsl, dict), "Missing compiled ActionDSL"
    assert isinstance(action_dsl.get("rules"), list), "Malformed ActionDSL rules"

    proof = checked_json(
        f"{GATEWAY}/api/v1/proofs/run",
        method="POST",
        expected=422,
        payload={"policy_hash": policy_hash, "action_dsl": action_dsl},
    )
    assert isinstance(proof, dict) and proof.get("status") == "failed", proof
    assert not proof.get("proof_hash"), "Unverified proof received a proof hash"
    assert proof.get("artifacts") == [], "Unverified proof returned artifacts"
    diagnostics = proof.get("diagnostics")
    assert isinstance(diagnostics, list) and diagnostics, "No proof refusal diagnostics"
    messages = " ".join(str(x.get("message", "")) for x in diagnostics if isinstance(x, dict))
    assert "sorry/admit" in messages, f"Unexpected proof refusal: {messages[:180]}"

    transaction_id = "ci-synthetic-transaction-001"
    ingested = checked_json(
        f"{DEMO}/api/ingest",
        method="POST",
        payload={
            "transaction_id": transaction_id,
            "amount": 25000,
            "merchant": "Casino",
            "user_id": "ci-user",
            "tenant_id": "ci-tenant-one",
            "location": "Offshore",
        },
    )
    assert isinstance(ingested, dict) and ingested.get("ok") is True

    denied = checked_json(
        f"{DEMO}/api/tx/{transaction_id}?tenant_id=ci-tenant-two",
        expected=404,
    )
    assert isinstance(denied, dict) and denied.get("ok") is False
    assert "different tenant" in str(denied.get("error", ""))

    fetched = checked_json(
        f"{DEMO}/api/tx/{transaction_id}?tenant_id=ci-tenant-one"
    )
    assert isinstance(fetched, dict) and fetched.get("ok") is True
    result = fetched.get("result")
    assert isinstance(result, dict) and isinstance(result.get("content"), list)
    rows = [x.get("text") for x in result["content"] if isinstance(x, dict)]
    assert rows, "Missing transaction lookup payload"
    transaction = json.loads(rows[0])
    assert transaction["id"] == transaction_id
    assert transaction["tenant_id"] == "ci-tenant-one"

    scored = checked_json(
        f"{DEMO}/api/score",
        method="POST",
        payload={"transaction_id": transaction_id, "tenant_id": "ci-tenant-one"},
    )
    assert isinstance(scored, dict) and scored.get("ok") is True
    score_content = scored.get("result")
    assert isinstance(score_content, dict) and score_content.get("content")
    score_payload = json.loads(score_content["content"][0]["text"])
    assert isinstance(score_payload.get("fraud_score"), (float, int))
    assert 0 <= score_payload["fraud_score"] <= 1

    return {
        "test_scope": "disposable_full_profile_deployment_and_synthetic_demo_http",
        "gateway_healthy_or_degraded": True,
        "demo_http_ready": True,
        "demo_http_tool_discovery": True,
        "policy_compilation_observed": True,
        "proof_http_status": 422,
        "proof_status": "failed",
        "proof_hash_issued": False,
        "placeholder_obligations_refused": True,
        "synthetic_transaction_ingestion_observed": True,
        "synthetic_cross_tenant_lookup_refused": True,
        "synthetic_fraud_score_returned": True,
        "real_policy_enforcement_verified": False,
        "certificate_provenance_verified": False,
        "independent_fraud_classification_validated": False,
        "replay_verification_performed": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = verify_contracts()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
