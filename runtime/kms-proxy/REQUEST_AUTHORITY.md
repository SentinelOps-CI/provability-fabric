# KMS request authority (candidate v1)

This contract replaces the legacy signature-prefix check and authorization caches.
It is a deployment-breaking candidate. The historical sidecar caller is removed in the cumulative candidate.
Any future caller needs an external issuer that authenticates the caller
and authorizes the exact request. The proxy
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

## Live provider and resource qualification

The dedicated CI fixture downloads Vault 1.21.4 from the publisher and
checks its archive against the pinned SHA-256 digest. It runs a disposable
loopback-only in-memory development server, provisions two independent
Ed25519 transit keys, and grants the proxy a short-lived token restricted
to signing with one key. A separately generated OpenSSL issuer signs
request bytes, and OpenSSL checks the returned Vault signature against
the public key obtained during fixture provisioning. Negative controls
cover changed data, unrelated verification key, missing request authority,
provider ACL denial and provider token revocation. The fixture does not
establish production Vault configuration, transport TLS, hardware-backed
custody or issuer authentication.

The Axum handler allows at most 32 simultaneous in-flight requests and
refuses additional work with HTTP 503. Body accumulation has a ten-second
deadline (HTTP 408) in addition to the existing 2 MiB bound. These defaults
are conservative engineering choices pending workload measurements.
They do not bound total process RSS, open TCP connections, or upstream
HTTP buffering. Provider requests retain their independent ten-second
timeout and 64 KiB response limit. Native tests of the new controls are
required before integration.


## Current migration boundary

The cumulative sidecar's log-ingestion path builds an incomplete certificate
candidate and rejects it before issuance if verified permission, witness,
label, epoch or bridge evidence is absent. It no longer invokes /kms/sign
or uses the old ATTESTATION_SIG fallback. The JWKS manager retains an
unused KMS URL field; that field is not evidence of a functioning KMS
caller. The Go MockKMSClient is test-oriented infrastructure, not a
compatible production issuer or cryptographic provider.

The independently executed cumulative qualification at c20e0ac1, workflow
46136377786, passed real disposable Vault signing, ACL denial and revocation
controls. That result supersedes earlier notes about pending native
qualification at older revisions. The test issuer is not a production
authority. Before production cutover:

1. Provision an independent issuer that establishes authenticated caller
   identity and permission over the exact key, operation and message.
2. Connect the sidecar only after verified execution-specific evidence is
   available; reject issuance in its absence.
3. Provision the proxy public key and allowlists separately from caller
   inputs; configure HTTPS Vault and least-privilege transit access.
4. Qualify migrated positive requests, all retired routes and issuer/key
   revocation against the intended deployment, including TLS.
5. Keep legacy artifacts distinguishable from newly issued signatures;
   never restore synthetic signing or downgrade to the prefix check.

Production provisioning and caller migration cannot be established by the
disposable test. Keep the incompatible candidate undeployed until these
obligations have actual evidence.
