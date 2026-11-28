# Sidecar signing profile candidate

The asynchronous signing pipeline previously emitted a custom BLAKE3 digest
over concatenated fields, then signed that digest. Its string-valued header
and empty byte-vector unprotected header did not implement COSE_Sign1.

This candidate defines a restricted RFC 9052 Sign1 profile using the
fully specified Ed25519 algorithm identifier -19 from RFC 9864. The protected
header is exactly CBOR map {1: -19}; the unprotected header is the empty
CBOR map. The Sig_structure uses the original protected and payload byte
strings, empty external AAD, and the context string Signature1. The signing
algorithm signs this CBOR array directly, not an application-specific hash.
The exported envelope is tagged with CBOR tag 18.

The application payload is a definite-length map, with a 32-byte byte string
for content_hash, unsigned timestamp, and issuer, subject and request_id
text strings, in the explicit order in cert_payload. This is a fixed
application encoding, not a general canonical CBOR implementation.

The convenience struct retains its existing Rust fields. Its unprotected
header now contains the encoded empty map (a0). Legacy payloads and
signatures differ and are not accepted as this profile. No automatic
fallback or relabeling of old signatures is provided. The public verify
method authenticates bytes under a caller-supplied trusted key; it does
not validate claim semantics or establish authority. It is not a general
COSE parser.

Repository search found the pipeline implementation/tests and performance
benchmarks, not a production call site. External consumers remain unknown.
This is a draft wire-protocol change requiring an explicit compatibility
decision before integration. The independent fixture is generated with a
minimal Python CBOR encoder and OpenSSL Ed25519, and native tests compare
six exact byte fields and reject mutations. Native Cargo must qualify
removal of serde_cbor and its unreachable half dependency before importing
the final generated lockfile.
