# Certificate-root data license

The retrieval gateway's SQLx Rustls configuration uses `webpki-roots` 0.26.11
and 1.0.12. The upstream project identifies the certificate data as Mozilla
trusted roots sourced from the Common CA Database (CCADB), distributed under
CDLA-Permissive-2.0.

- Upstream: https://github.com/rustls/webpki-roots
- License: https://cdla.dev/permissive-2-0/

The Cargo Deny exceptions apply only to the two exact package versions.
The general license allowlist and advisory checks are unchanged. The source
repository does not vendor the root data. The retrieval gateway Docker build
copies the original LICENSE from each resolved crate into
`/usr/share/doc/retrieval-gateway/third-party-licenses/`; CI checks the final
image for those files. For other binary distributions that embed the root
data, include the applicable upstream license texts with the distribution.
Revisit the inventory and exceptions when updating the root packages.
