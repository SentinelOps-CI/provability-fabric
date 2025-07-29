# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

package provability

default allow = false

allow {
    input.request.kind.kind == "Pod"
    spec := input.request.object.metadata.annotations["spec.sig"]
    io.jwt.verify("sigstore", spec)
    not revoked_signer(spec)
}

revoked_signer(spec) {
    # Check if signature starts with "revoked:" (legacy check)
    startswith(spec, "revoked:")
}

revoked_signer(spec) {
    # Check against revocation list from JSON file
    revocation := data.revocations[_]
    revocation.sig == spec
}

# Helper function to extract signature hash from full signature
extract_sig_hash(spec) {
    parts := split(spec, ":")
    count(parts) >= 3
    parts[2]  # Return the hash part
}

revoked_signer(spec) {
    # Check against revocation list using hash only
    sig_hash := extract_sig_hash(spec)
    revocation := data.revocations[_]
    revocation.sig == sig_hash
}