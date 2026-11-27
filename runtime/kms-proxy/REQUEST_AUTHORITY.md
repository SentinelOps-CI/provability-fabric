# KMS request authority (candidate v1)

This contract replaces the legacy signature-prefix check and authorization caches.
It is a deployment-breaking candidate. Existing sidecar callers need an external
issuer that authenticates the caller and authorizes the exact request. The proxy
does not establish hardware attestation, issue credentials, or manage issuer keys.

## Operator configuration

- `KMS_ATTESTATION_PUBLIC_KEY`: standard-base64 Ed25519 verifying key (32 bytes).
- `KMS_ATTESTATION_AUDIENCE`: exact, deployment-specific audience.
- `KMS_ALLOWED_POLICY_HASHES`, `KMS_ALLOWED_POD_IDENTITIES`: comma-separated
  nonempty allowlists, matched exactly after trimming configuration entries.
- `VAULT_URL`: root HTTPS Vault transit endpoint (literal loopback HTTP is
  supported for isolated development tests).
- `VAULT_TOKEN`: operator-provisioned token restricted to intended transit signing
  keys. Redirects are disabled; provider calls have a ten-second timeout.

Missing or invalid authority configuration denies signing. Missing or failing
Vault configuration produces a failure response, never a synthetic signature.
The only implemented operation is POST /kms/sign. Other legacy cryptographic
operations and key rotation return HTTP 501.

## Signature format

The existing request has operation, key_id, optional data, and an
attestation_token containing token (identifier), pod_identity, policy_hash,
timestamp, and signature. The signature is standard-base64 Ed25519 over the
following byte string, in order:

1. ASCII domain string `provability-fabric/kms-request-authority/v1` followed by NUL.
2. Audience, token identifier, pod identity, policy hash, operation, and key ID,
   each as UTF-8 preceded by its unsigned 32-bit big-endian byte length.
3. Unix timestamp seconds (signed 64-bit big-endian), followed by nanoseconds
   (unsigned 32-bit big-endian). Leap-second representations are rejected.
4. One byte 0 for absent data; otherwise one byte 1 followed by its unsigned
   32-bit big-endian UTF-8 byte length and UTF-8 bytes.

The signature itself is excluded. The issuer must sign the actual intended key,
operation and message, not a mutable template. A token is checked on every
request against the independent public key, audience and both allowlists.
The sampled clock must satisfy 0 <= age <= 60 seconds, including subsecond
precision. There is no grace period for future timestamps. Clock synchronization
is an operational prerequisite. Identical authenticated requests remain
replayable within the accepted window; exactly-once execution is not claimed.

Collected request bodies are limited to 2 MiB and collected provider response
bodies to 64 KiB. These bounds concern collected bytes, not total transport
memory consumption. Key identifiers are restricted to a single ASCII alphanumeric,
underscore or hyphen segment (1–128 bytes).

## Qualification boundaries

Native tests use an isolated deterministic issuer and a loopback synthetic
provider to exercise actual signature verification and HTTP transport. The
provider fixture's signature-shaped output is not evidence of cryptographic
signing by Vault. The production issuer, credential provisioning and rotation,
sidecar migration, live Vault signing and independent signature verification
require separate qualification before deployment. The existing Rust HTTP
dependency advisories are tracked separately in #315.

## Timestamp implementation migration

The candidate uses pinned `time 0.3.47` and accepts the supported RFC 3339
domain (UTC years 0000–9999, at most nine fractional digits, no leap seconds).
Offsets normalize to UTC; JSON serialization uses Z and 0, 3, 6 or 9
fractional digits. The signature input continues to encode signed Unix seconds
and unsigned nanoseconds, not the textual spelling of the timestamp.
The freshness interval is closed at both zero and 60 seconds and evaluated
at nanosecond precision.

Four frozen signature vectors were generated independently with Python
`struct.pack` and `cryptography` Ed25519. The Rust tests compare SHA-256 of
the exact signed bytes, verify the independent signatures, and check the
serialized request round trip. The cases cover nonzero UTC offset, negative
Unix seconds, absent data and empty data. The fixture issuer key is public,
deterministic test material only. Native checks of the migrated implementation
are pending.

## Consolidated transport candidate

This branch ports the authority implementation to Axum 0.7.9 and Reqwest
0.12.28, retaining the exact signed-request encoding and timestamp codec.
The HTTP request body is accumulated under the existing 2 MiB bound, including
streamed chunks. The operator's Vault endpoint is parsed before path
construction; environment-configured proxies and redirects are disabled for
the provider client. Native loopback tests exercise the actual Axum listener
as well as the synthetic provider fixture.

The lockfile's KMS dependency edge is reconciled provisionally. Native Cargo
must remove the now-unreachable Chrono package and verify that no registry
version or checksum has changed before its artifact is imported. All
deployment and independent issuer obligations remain open. This candidate
must not be deployed merely because its dependency scan succeeds.
