# Retrieval gateway authorization contract (candidate)

This document describes the **proposed, deployment-breaking** strict
authorization boundary implemented in the security-candidate branch. It is
not evidence of a production deployment or an approved issuer integration.

## Incoming capabilities

`POST /query` accepts its existing `QueryRequest` JSON fields:
`query`, `tenant`, `subject_id`, `capability_token`,
`labels_filter`, and optional `limit`. The capability token is a compact
JWT in the form `base64url(header).base64url(claims).base64url(signature)`,
signed with Ed25519 over the exact ASCII `header.payload` bytes. The
protected header contains exactly `alg: EdDSA`, `typ: JWT`, and a
nonempty trusted `kid`.

The authenticated JSON payload has the following **mandatory** fields.

| Field | Semantics |
| --- | --- |
| `iss` | Exact deployment-configured issuer |
| `aud` | Exact string `pf-retrieval-gateway` |
| `sub` | Request subject identifier, matched exactly |
| `tenant` | Request tenant identifier, matched exactly |
| `iat` | Unix issuance time in seconds |
| `nbf` | Unix not-before time in seconds |
| `exp` | Unix expiration in seconds |
| `jti` | Nonempty token identifier for trace correlation |
| `allowed_labels` | Explicit list of label names |
| `capabilities` | Explicit list of authorized capability names |

There is no implicit public label, wildcard label, or default access. The
verifier rejects unknown issuer, key, algorithm, type, audience, tenant,
subject, expired or premature tokens, duplicate scopes, lifetime above one
hour, and issuance more than 30 seconds ahead of server time. The signer
must encode integer timestamps in seconds and protect the full payload.
There is no external JWKS fetch or caller-controlled key URL.

Configure **public verifier keys only** through the
`RETRIEVAL_JWT_VERIFY_KEYS_JSON` environment variable. It contains a
nonempty JSON object mapping unique `kid` values to unpadded base64url
encodings of raw 32-byte Ed25519 *public* keys. Set `RETRIEVAL_JWT_ISSUER`
to the trusted issuer identifier. Missing or malformed configuration
prevents the process from starting. The private signing keys must remain
under issuer control, outside this repository and its build images.
Overlapping trusted key identifiers support controlled rotation, and
removing a key revokes tokens signed by it.

**No compatible deployed issuer, key distribution, or rollback plan has yet
been established.** This candidate must not be merged or deployed until
positive authorized and negative forged/expired/wrong-tenant credentials
have been exercised in disposable infrastructure and existing callers have
been migrated.

## Policy evaluation

The runtime accepts only strict default-deny and tenant isolation policy
configuration. Each request must name one or more labels present in the
signed `allowed_labels` list. Each label must have a defined policy rule.
Supported rules are conjunctions of exact predicates.

The `tenant_match` predicate checks the bound tenant and matching index
shard. `subject_authorized` needs a signed `private_access` capability.
`elevated_privileges` needs both a signed capability and a matching
subject rule. `capability:name` needs a named policy capability and that
signed capability. The `audit_log` and `dp_budget_available` predicates
deny while no durable audit recorder or budget enforcement is installed.
This is intentional; debug logging is not an audit record or privacy-budget
certificate. Unknown policy predicates fail configuration validation.
Labels not listed in the policy are denied.

Returned documents must carry at least one label, and **every** document
label must be within the authorized query label set. Documents classified
both public and secret are denied to public-only requests. A requested
result limit must be positive and within the configured maximum. Cache reuse is restricted to the exact query hash, tenant, label set and
result limit. The cache is not an independent authorization boundary.

Until authenticated ownership and administrative scopes have been defined,
`GET /receipts`, `GET /cache/stats`, and
`POST /cache/invalidate/:tenant` are deliberately not registered by this
candidate. Existing callers of these endpoints need a reviewed replacement
contract. `GET /health` remains public and contains no tenant data.

## Verification boundaries

A valid EdDSA token authenticates signer-issued claims and their binding to
the request. It does not prove the issuer's identity governance, correct
issuance, replay prevention, durable auditing, revocation of individual
tokens, end-to-end tenant isolation, storage correctness, or the integrity
of external ledger delivery. Bearer tokens are replayable during their
validity interval. Key removal is the only revocation mechanism currently
implemented. Clock skew is tolerated only for issuance time, not for expiry
or not-before checks.

Before production integration, establish a responsible issuer, stable trust
roots, credential rollout, negative-control fixtures for multiple tenants,
operational telemetry, and signed-credential integration tests. The project
issue tracking these obligations is #297.

## Independently seeded handler regression

The Rust unit suite also constructs a separate in-memory corpus containing
two tenants, two authorized public documents, a private document, and a
public-plus-secret mixed-classification document. It invokes the production
`handle_query` function with authenticated signed credentials and verifies
exact document identifiers and receipt tenant binding. Separate checks reject
untrusted signatures, wrong-tenant binding, missing private capability, and
secret retrieval. A sequence of limit-one and limit-ten public requests
checks that the authorization-sensitive cache does not reuse the smaller
result set for the larger request.

These seeded checks exercise the real query handler, ABAC evaluator, in-memory
index, and Ed25519 signer. They are in-process tests rather than external
HTTP/ledger experiments and do not establish PostgreSQL adapter isolation,
ledger persistence, operational audit, or a deployed issuer trust model.
The reconciled mainline includes transaction-local tenant binding, complete
label containment, and separate PostgreSQL RLS tests. The serving binary
still uses the in-memory index; a seeded network-facing PostgreSQL service
and production issuer integration remain separate obligations (issue #304).

## Disposable signed HTTP validation

The full-profile Compose smoke provisions two independent temporary Ed25519
private keys, one for receipt signing and one for disposable JWT issuance.
It exports the JWT **public** key to
`PF_RETRIEVAL_JWT_VERIFY_KEYS_JSON`, sets `PF_RETRIEVAL_JWT_ISSUER`, and
exercises 15 real HTTP `/query` controls with signed and invalid credentials.
Associated negative-control tests use independent OpenSSL verification of
the compact JWT signature and refuse unexpected authorization responses.

Ordinary manual full-profile startup must receive the public-key JSON map
and trusted issuer through those environment variables; empty values fail
gateway startup. This smoke uses an unseeded in-memory index, and its
two accepted public requests must return zero documents. It confirms the
authenticated admission path, not tenant isolation, document correctness,
independent receipt provenance, or a production-compatible token issuer.
Signed tokens remain replayable until expiry; there is no refresh or
per-token revocation service.

The YAML declares tenant/subject request-rate limits and a concurrent-query
limit. The current Rust handler retrieves matching rate configurations yet
does not enforce counters or concurrency admission. These controls are
**unimplemented**, and a green HTTP smoke does not establish quota or abuse
resistance. Receipt submission is also best-effort: a ledger failure is
logged and the query still returns success. A signed local receipt is not
proof of ledger persistence.


## Opt-in PostgreSQL serving mode

Set `RETRIEVAL_POSTGRES_URL` to a dedicated restricted SELECT role after
administrator-run schema migration. The gateway rejects empty or invalid
configuration, owners, superusers, RLS bypass roles, roles with table write
privileges, and missing forced RLS or restrictive guard. This startup check
does not establish policy expression correctness or the absence of indirect
privileges. Operators must verify the actual database policy and trust the
administrator. Absence of the variable preserves the historical memory mode.

PostgreSQL serving bypasses the result cache because document labels and
contents are mutable independently of the gateway. A database read failure
returns HTTP 500 rather than cached results or an empty memory response.
`RETRIEVAL_LISTEN_ADDR` optionally selects the listener address.

The disposable pgvector CI fixture exercises the actual serving binary and
independently generated issuer and receipt keys. It checks exact returned
identifiers, signed receipt commitments, concurrent tenant requests, label
changes and revoked database SELECT access. It is not a production issuer
rollout, ledger-persistence test or general proof of mediation.
