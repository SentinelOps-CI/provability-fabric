"""Independent fixture checks for the Rust retrieval gateway's HTTP contract.

These checks validate shape, attribution, and corpus correspondence. They do
not verify receipt signatures or establish authentication-key trust.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def load_reference_documents(path: str | Path) -> dict[str, dict[str, Any]]:
    """Read a reference manifest for an independently seeded test corpus.

    The reference file must be prepared independently of responses returned by
    the system under test; copying service responses into it invalidates the
    cross-tenant oracle.
    """
    manifest = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
        raise ValueError("reference manifest requires schema_version 1")
    documents = manifest.get("documents")
    if not isinstance(documents, list) or not documents:
        raise ValueError("reference manifest requires nonempty documents list")
    known: dict[str, dict[str, Any]] = {}
    for doc in documents:
        if not isinstance(doc, dict):
            raise ValueError("reference document must be an object")
        identifier = doc.get("document_id")
        tenant = doc.get("tenant")
        labels = doc.get("labels")
        digest = doc.get("content_sha256")
        if not isinstance(identifier, str) or not identifier or identifier in known:
            raise ValueError("document_id missing or duplicated")
        if not isinstance(tenant, str) or not tenant.strip():
            raise ValueError("reference document tenant missing")
        if not isinstance(labels, list) or not labels or any(
            not isinstance(x, str) or not x for x in labels
        ):
            raise ValueError("reference document labels invalid")
        if len(set(labels)) != len(labels):
            raise ValueError("reference document contains duplicate labels")
        if not isinstance(digest, str) or len(digest) != 64 or any(
            c not in "0123456789abcdef" for c in digest
        ):
            raise ValueError("reference document requires lowercase SHA-256 digest")
        known[identifier] = {"tenant": tenant, "labels": frozenset(labels), "content_sha256": digest}
    tenants = {doc["tenant"] for doc in known.values()}
    if len(tenants) < 2:
        raise ValueError("cross-tenant reference corpus needs at least two tenants")
    for tenant in tenants:
        if not any(doc["tenant"] == tenant and "public" in doc["labels"] for doc in known.values()):
            raise ValueError(f"tenant {tenant!r} needs a known public positive-control document")
    return known


def inspect_query_response(
    payload: Any,
    *,
    expected_tenant: str,
    expected_subject: str,
    requested_labels: list[str],
    known_documents: dict[str, dict[str, Any]],
) -> tuple[int, bool, bool]:
    """Return (result_count, cross_tenant, unauthorized_or_tampered).

    A valid signed-looking receipt is checked for shape and attribution only.
    Signature verification is a separate, unfulfilled obligation.
    """
    if not isinstance(payload, dict):
        raise ValueError("retrieval response must be an object")
    results = payload.get("results")
    if not isinstance(results, list):
        raise ValueError("retrieval response requires results array")
    if type(payload.get("total_count")) is not int or payload["total_count"] != len(results):
        raise ValueError("retrieval total_count is inconsistent")
    receipt = payload.get("receipt")
    if not isinstance(receipt, dict):
        raise ValueError("retrieval receipt missing")
    if receipt.get("tenant") != expected_tenant or receipt.get("subject_id") != expected_subject:
        raise ValueError("retrieval receipt subject/tenant mismatch")
    if receipt.get("index_shard") != f"shard_{expected_tenant}":
        raise ValueError("retrieval receipt index_shard mismatch")
    if type(receipt.get("result_count")) is not int or receipt["result_count"] != len(results):
        raise ValueError("retrieval receipt count mismatch")
    if receipt.get("sign_alg") != "ed25519" or not isinstance(receipt.get("sig"), str) or not receipt["sig"]:
        raise ValueError("retrieval receipt lacks signature metadata")

    cross_tenant = False
    unauthorized = False
    for result in results:
        if not isinstance(result, dict):
            raise ValueError("retrieval result must be an object")
        identifier = result.get("document_id")
        content = result.get("content")
        labels = result.get("labels")
        reported_digest = result.get("content_hash")
        if not isinstance(identifier, str) or not identifier:
            raise ValueError("retrieval result missing document_id")
        if not isinstance(content, str):
            raise ValueError("retrieval result missing content")
        if not isinstance(labels, list) or any(not isinstance(x, str) for x in labels):
            raise ValueError("retrieval result labels invalid")
        if not isinstance(reported_digest, str) or len(reported_digest) != 64:
            raise ValueError("retrieval result content_hash invalid")
        computed_digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
        if reported_digest != computed_digest:
            unauthorized = True
        known = known_documents.get(identifier)
        if known is None:
            unauthorized = True
            continue
        if known["tenant"] != expected_tenant:
            cross_tenant = True
        if known["content_sha256"] != computed_digest or known["labels"] != frozenset(labels):
            unauthorized = True
        if requested_labels and not known["labels"].intersection(requested_labels):
            unauthorized = True
    return len(results), cross_tenant, unauthorized
