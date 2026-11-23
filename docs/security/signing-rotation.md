# Signing & Rotation Procedure

This guide describes how to configure a pluggable signer and rotate keys.

## Configuring the signer

- file backend:
  - set `CERT_SIGNER_BACKEND=file`
  - set `CERT_SIGNER_FILE=/path/to/ed25519.pem`

- kms/vault backends:
  - not implemented. Configuring either backend fails startup until a production signing provider is implemented and tested.

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

The service fetches and validates the approved JWKS **once at startup**,
using a five-second deadline, a 1 MiB response limit, HTTPS certificate
validation, and no redirect following. An unreachable or invalid configured
endpoint prevents startup. Subsequent validation requests use only the
in-memory public-key snapshot; request bodies never cause outbound JWKS
requests. Rotate keys by updating the approved JWKS and restarting the
service after independent trust-root approval. Pin the final URL and operate
its DNS and TLS trust under deployment control.

A caller-supplied `pem_pub` is rejected with HTTP 400
(`UNTRUSTED_VERIFIER_KEY`). A request cannot establish its own issuer
authority by supplying both a signed certificate and the matching public
key. `signature_valid=true` is returned only after verification against
public keys loaded from the operator-configured JWKS at service startup.
If no trusted verifier keys are configured, signed requests receive
`signature_valid=false` with `trusted_verifier_unavailable`.

Local verification against an arbitrary caller-owned PEM must happen in
an explicitly labeled, offline diagnostic tool; it is never an issuer
trust decision of the evidence-service HTTP API. This is a breaking
change for console or other callers supplying `pem_pub` and must be
reflected in any client migration.

This restriction does not implement key-ID binding, rotation, revocation,
certificate-claim validation or an independently provisioned issuer trust
contract. Those requirements must be addressed before trusting certificates
for authorization or compliance decisions.
