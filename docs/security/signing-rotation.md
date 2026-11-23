# Signing & Rotation Procedure

This guide describes how to configure a pluggable signer and rotate keys.

## Configuring the signer

- file backend:
  - set `CERT_SIGNER_BACKEND=file`
  - set `CERT_SIGNER_FILE=/path/to/ed25519.pem`

- kms/vault backends:
  - placeholders; integrate with your provider and set `CERT_SIGNER_BACKEND=kms|vault`

## Rotation steps

1. Generate new key pair.
2. Publish public key via JWKS endpoint.
3. Update signer to use the new private key.
4. Overlap old/new keys in JWKS for a grace period.
5. Remove the old key after downstreams observe new signatures.

## Testing JWKS validation (CI)

- Use `.github/workflows/jwks-validate.yml` to validate CERT signatures using a JWKS URL.

## Evidence-service JWKS request boundary

The evidence service's `POST /api/v1/evidence/validate` endpoint accepts a
`jwks_url` field only when it matches the exact operator-provisioned
`EVIDENCE_TRUSTED_JWKS_URL` value. The setting is optional; when absent, the
service refuses all request-driven remote JWKS fetches. An invalid configured
endpoint (anything other than an absolute HTTPS URL, or one containing
userinfo or a fragment) prevents startup.

A configured JWKS fetch has a five-second deadline, a 1 MiB response limit,
and no redirect following. Pin the final URL and operate its DNS and TLS
trust under deployment control. A caller-supplied `pem_pub` continues to
support local cryptographic diagnostics, but a signature verified under a
key supplied by that same caller does **not** establish an authorized issuer
or trusted certificate provenance.

This restriction does not implement key-ID binding, rotation, revocation,
certificate-claim validation or an independently provisioned issuer trust
contract. Those requirements must be addressed before trusting certificates
for authorization or compliance decisions.
