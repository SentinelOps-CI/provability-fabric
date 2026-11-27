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
