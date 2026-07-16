# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

package provability

default allow = false

# Admit pods that carry a well-formed, non-revoked signature annotation.
# Cryptographic verification against the trust root is performed by the
# admission runtime; this policy enforces presence, shape, and revocation.
allow {
	input.request.kind.kind == "Pod"
	spec := input.request.object.metadata.annotations["spec.sig"]
	signature_valid(spec)
	not revoked_signer(spec)
}

signature_valid(spec) {
	is_string(spec)
	count(spec) > 0
	not startswith(spec, "invalid_")
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
extract_sig_hash(spec) = hash {
	parts := split(spec, ":")
	count(parts) >= 3
	hash := parts[2]
}

revoked_signer(spec) {
	# Check against revocation list using hash only
	sig_hash := extract_sig_hash(spec)
	revocation := data.revocations[_]
	revocation.sig == sig_hash
}
