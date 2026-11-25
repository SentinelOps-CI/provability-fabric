# Evidence HTTP access candidate

Certificate storage, search, session lookup and compliance packet diagnostics
are scoped to an authenticated tenant. Health and detached signature
validation remain public; archive download remains unavailable.
A valid access credential does not establish the truth of evidence claims.

Set `EVIDENCE_ACCESS_FILE` to an operator-owned JSON file mounted read-only
outside the source tree and build context. It contains an array of objects
with `tenant`, `token_sha256`, `read` and `write`. Generate a separate
cryptographically random 32-byte credential for each principal; distribute
its unpadded base64url representation over a protected channel and place the
lowercase hexadecimal SHA-256 digest of the original bytes in the file.
Clients send `Authorization: Bearer <token>` through authenticated TLS.

Duplicate digests, malformed configuration and entries with no permissions
are rejected. Missing configuration leaves protected operations unavailable.
Missing or invalid credentials are rejected; mismatched tenant or permission
is forbidden. Omitted search tenant filters are replaced with the
authenticated tenant. Rotation requires replacing the operator file and
restarting. This mechanism does not establish individual user identity
inside a tenant, durable audit, replay protection, or live revocation.

HTTP certificate storage is unsigned only in this candidate. If a service
signer is configured, HTTP issuance refuses the request until an independently
qualified provenance-verification path exists. Existing unsigned records
are not promoted to trusted evidence.

This is an intentionally incompatible draft for issue #345. Existing clients,
deployment provisioning, TLS termination, database permissions, and proof
provenance must be reconciled before release. Access tests are not evidence
of independent certificate issuance authority.

Database operations bind tenant identity with transaction-local `set_config`.
Reads use a repeatable-read, read-only transaction for count and result queries.
Database searches with no tenant are refused. The restricted-role integration
fixture separates schema administration from runtime operations and checks
pooled-connection reuse. Production startup still performs schema DDL; a
separately provisioned migration identity is a remaining deployment obligation.
