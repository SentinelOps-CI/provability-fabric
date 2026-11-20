# Retrieval result commitment v2

Status: implemented for newly generated retrieval-gateway access receipts.
The historical receipt signature envelope and its canonical JSON field names are
unchanged. This specification defines the byte-level meaning of the signed
`result_hash` field for new receipts.

## Version distinction

- **Legacy v1:** exactly 64 hexadecimal SHA-256 characters. Historical gateway
  generation concatenated every result's `document_id` and `content` bytes without
  field boundaries. This format has ambiguous encodings and does not attest to
  classifications, metadata, scores, or the tenant.
- **V2:** the exact lowercase ASCII prefix `sha256-v2:` followed by 64
  lowercase hexadecimal SHA-256 characters. The prefix is part of the
  `result_hash` string covered by the receipt's existing canonical Ed25519
  signature. It is not an unsigned indication or an inferred digest version.

Consumers must distinguish these formats explicitly. Signature verification of
a historical v1 receipt establishes only the exact legacy signed fields and
legacy result hash semantics. It does not establish the stronger v2 commitment.

## V2 preimage

The digest is SHA-256 of the following byte sequence, with no field separators
other than those described below.

1. The ASCII domain `provability-fabric/retrieval-result/v2` followed by one
   NUL byte (hex `00`).
2. Tenant string, encoded as an unsigned 64-bit big-endian UTF-8 byte length,
   then the original UTF-8 bytes.
3. Result count encoded as unsigned 64-bit big-endian.
4. For each result **in the exact response order**, append:
   - `document_id`, `content`, and `content_hash` in that order, each
     encoded with the same length-prefixed UTF-8 representation.
   - `score` as IEEE-754 binary64, big-endian, with negative zero encoded
     as positive zero; non-finite scores are rejected before signing.
   - Label count as unsigned 64-bit big-endian, followed by each label as a
     length-prefixed UTF-8 string in its original array order.
   - Metadata entry count as unsigned 64-bit big-endian, followed by the
     string key and string value of each entry as length-prefixed UTF-8.
     Entries are ordered by the unsigned lexicographic comparison of the UTF-8
     key bytes. The source map's iteration order is irrelevant.

All counts and string byte lengths must fit in 64 bits. Strings are not
Unicode-normalized or case-folded. The tenant is the query-context string passed to receipt generation;
authorization of that context is assessed separately. The result items do not
carry a separate tenant property. Changing that tenant or any bound response field
alters the commitment except for the documented zero normalization and
metadata entry ordering.

## Verification

The reference fixture is
`tests/fixtures/crypto/retrieval_result_commitment_v2.json`.
Rust tests in `runtime/retrieval-gateway/src/result_commitment.rs` compare their
output with five fixed vectors. A separate Python standard-library
implementation in `tests/test_retrieval_result_commitment_v2.py`
independently checks those vectors and negative controls. The second fixture,
`tests/fixtures/crypto/retrieval_receipt_v2_signed.json`, contains a fixed
Ed25519-signed v2 receipt and its test public key. The existing Go and
TypeScript receipt verifiers validate that signature and reject changes to
the signed prefix or digest. The retrieval gateway workflow executes the
Rust, Python, Go, and TypeScript regression suites.

To establish that a receipt commits to a **particular response**, a verifier
must confirm the receipt's canonical Ed25519 signature using its configured
trusted public key, validate the declared signed version, compute the v2 digest
from the received tenant and full result list, and compare the complete
version-prefixed string to the signed `result_hash`. A valid signature alone
does not establish that a verifier has received, reconstructed, or checked
the result data.

The digest binds fields, not the correctness of authorization decisions,
data provenance, content-hash semantics, or actual execution containment.
The current in-memory gateway's storage and token-enforcement properties
have separate security issues. Existing v1 receipts remain distinguishable
and readable; they are never relabeled as v2 evidence.

## Compatibility

V2 extends the signed value of an existing string field, without adding a
new canonical receipt field. The existing Rust, Go, and TypeScript signing
and verification payload definitions include the entire `result_hash`
string. The ledger's Prisma model stores it as an unrestricted string. The
gateway receipt schema accepts the explicit legacy-v1 or v2 syntax.

Downstream integrations that impose a hard 64-character digest limit need
to adopt the versioned syntax before using v2-producing gateways.
No migration of old ledger records, re-signing of historical receipts, or
automatic upgrade of legacy integrity claims is performed by this change.
