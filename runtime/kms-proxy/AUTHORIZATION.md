# KMS signing authorization candidate

This candidate deliberately replaces the former prefix-signature and cache
authorization simulation. Only signing is implemented. Each request must
carry an Ed25519 signature issued by a configured independent authority.
Missing configuration, invalid tokens, unsupported operations and provider
failures return no successful result. Key rotation has no HTTP implementation.

Configure KMS_ATTESTATION_PUBLIC_KEY (standard base64, raw 32-byte public
key), KMS_ALLOWED_POD_IDENTITY, KMS_ALLOWED_POLICY_HASH and KMS_KEY_ID.
The key identifier is restricted to ASCII letters, digits, underscore and
hyphen. This version supports one explicit authority/scope. Configure an
authenticated HTTPS Vault endpoint and token, or a trusted HTTPS signing
gateway implementing POST /sign. The gateway is not the AWS KMS API.
No provider substitution occurs after failure of a selected provider.

Signature transcript: ASCII PF-KMS-AUTHORIZATION-v1 followed by a NUL;
then each UTF-8 field framed by its unsigned 64-bit big-endian byte count,
in order: token, pod_identity, policy_hash, operation, key_id, data.
Append signed 64-bit big-endian Unix seconds and unsigned 32-bit big-endian
nanoseconds. Sign these bytes with Ed25519 and encode the 64-byte signature
as standard base64. Token freshness is measured against the service clock;
future values and ages greater than 60 seconds are denied.

The issuer must independently establish the attestation and authority.
The service does not verify hardware measurements, prevent replay of an
identical signed request within its validity period, implement live key
rotation, or establish actual provider correctness. Existing clients and
operator provisioning must be migrated before deployment. The native
loopback regression uses a disposable issuer and a recording test provider;
it does not establish real Vault or cloud KMS integration.
