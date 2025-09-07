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
