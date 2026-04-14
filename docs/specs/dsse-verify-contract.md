# DSSE verify contract (v1)

This document defines the v1 contract for verifying DSSE (Dead Simple Signing Envelope) signatures used for receipts and CERT-style signatures across the platform.

## Scope

- **Receipts:** retrieval-gateway access receipts; verifiers must validate DSSE envelope and payload binding.
- **CERT/signing:** sidecar-watcher CERT-V1 emissions; evidence-service verify API; CLI/console cert verify.

## Algorithm and format

- **Signature algorithm:** Ed25519.
- **Payload canonicalization:** Deterministic JSON (canonical key order, no extra whitespace). Exact format is payload-type specific (e.g. access receipt uses a fixed schema).
- **PayloadType binding:** The DSSE envelope includes `payloadType` (e.g. `application/vnd.provability-fabric.access-receipt`). Verifiers must reject if payloadType does not match expected value for the context.
- **Envelope structure:** Standard DSSE: `payload` (base64), `payloadType`, `signatures` (array of `keyid`, `sig`).

## Trust root supply

- **Default (v1):** Static public key file. Verifiers are configured with a path to a PEM file (Ed25519 public key) or with the PEM content (e.g. env var). No default or in-process key; if unset, verification fails or is skipped with a clear "not configured" outcome.
- **Optional:** JWKS URL. Verifiers may be configured with a JWKS endpoint URL; they fetch keys and try each applicable key until one verifies. Used for rotation and multi-tenant key sets.

## Verifier behavior

1. Decode DSSE envelope (base64 payload, parse JSON signatures).
2. Verify payloadType matches expected for the operation.
3. Resolve public key: from PEM (file or env) or from JWKS (by key id or try all).
4. Verify Ed25519 signature over canonical payload (payload bytes, not base64-encoded string).
5. Reject if any step fails; do not fall back to a placeholder or "accept" without verification.

## Fixtures for tests

Shared fixtures live under `tests/fixtures/crypto/`: Ed25519 key pair (PEM), sample DSSE envelope (payload + signature). Tests in Go, Rust, and TypeScript use these to assert verify accepts valid envelope and rejects modified payload or signature.
