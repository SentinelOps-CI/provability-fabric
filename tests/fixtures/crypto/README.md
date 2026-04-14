# Crypto fixtures for cross-language DSSE and Ed25519 tests

Used by Go (evidence-service, policy-kernel), Rust (sidecar-watcher, retrieval-gateway), and TypeScript tests to verify DSSE envelopes and Ed25519 signatures using fixture keys (no hardcoded or default keys in code).

## Contents

- **ed25519_public.pem** – Ed25519 public key (PEM, PKCS#8 or OpenSSL format). Used by verifiers.
- **ed25519_private.pem** – Ed25519 private key (PEM). Used by signers in tests only; never in production.
- **dsse_sample_envelope.json** – Sample DSSE envelope (payloadType, payload base64, signatures) for access receipt or CERT payload type. Signature is produced with the fixture private key over the payload.

## Generation

Fixtures are checked in. To regenerate deterministically (optional):

    python scripts/generate_crypto_fixtures.py

Requires: Python 3.8+, `cryptography` (pip install cryptography).

## Usage

- **Verifiers:** Load `ed25519_public.pem` and verify signature in DSSE envelope over payload.
- **Signers (tests only):** Load `ed25519_private.pem` to produce signatures in unit tests.
- **Contract:** See [docs/specs/dsse-verify-contract.md](../../../docs/specs/dsse-verify-contract.md).
