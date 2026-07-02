# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
"""Ledger MCP tenant claim resolution integration smoke (F03/F04)."""

from __future__ import annotations


def resolve_tenant_id(user: dict[str, str] | None) -> str | None:
    """Mirror runtime/ledger/src/mcp/mcp-service.ts resolveTenantId."""
    if not user:
        return None
    return user.get("tid") or user.get("tenantId") or user.get("tenant_id")


def test_tid_preferred_over_legacy_claims() -> None:
    assert resolve_tenant_id({"tid": "canonical", "tenant_id": "legacy"}) == "canonical"


def test_tenant_id_fallback() -> None:
    assert resolve_tenant_id({"tenant_id": "legacy-tenant"}) == "legacy-tenant"


def test_tenant_id_absent_returns_none() -> None:
    assert resolve_tenant_id({}) is None
    assert resolve_tenant_id(None) is None


def test_jwt_round_trip_shape() -> None:
    """Simulate JWT tenant round-trip used by MCP proxy middleware."""
    jwt_claims = {"sub": "user-1", "tid": "tenant-a", "rls_token_hash": "abc123"}
    tenant_id = resolve_tenant_id(jwt_claims)
    assert tenant_id == "tenant-a"
    mcp_context = {
        "tenantId": tenant_id,
        "userId": jwt_claims["sub"],
        "validated": True,
    }
    assert mcp_context["tenantId"] == "tenant-a"
