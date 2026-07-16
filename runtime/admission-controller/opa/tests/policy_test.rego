# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

package provability

# Test case: Allow valid signature
test_allow_valid_signature {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "valid_signature_here"},
				},
			},
		},
	}

	allow with input as input_doc
}

# Test case: Deny revoked signature (legacy prefix)
test_deny_revoked_signature {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "revoked:some_signature"},
				},
			},
		},
	}

	not allow with input as input_doc
}

# Test case: Deny invalid signature marker
test_deny_invalid_signature {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "invalid_signature"},
				},
			},
		},
	}

	not allow with input as input_doc
}

# Test case: Deny missing spec.sig annotation
test_deny_missing_spec_sig {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {"metadata": {"annotations": {}}},
		},
	}

	not allow with input as input_doc
}

# Test case: Deny non-Pod resource
test_deny_non_pod_resource {
	input_doc := {
		"request": {
			"kind": {"kind": "Service"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "valid_signature"},
				},
			},
		},
	}

	not allow with input as input_doc
}

# Test revoked_signer function
test_revoked_signer_true {
	revoked_signer("revoked:some_signature")
}

test_revoked_signer_false {
	not revoked_signer("valid_signature")
}

# Revocation list: full signature match
test_deny_revocation_list_full_sig {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "blocked_full_sig"},
				},
			},
		},
	}

	not allow with input as input_doc with data.revocations as [{"sig": "blocked_full_sig"}]
}

# Revocation list: hash extracted from colon-delimited signature
test_deny_revocation_list_hash {
	input_doc := {
		"request": {
			"kind": {"kind": "Pod"},
			"object": {
				"metadata": {
					"annotations": {"spec.sig": "algo:key:deadbeef"},
				},
			},
		},
	}

	not allow with input as input_doc with data.revocations as [{"sig": "deadbeef"}]
}

test_extract_sig_hash {
	extract_sig_hash("algo:key:deadbeef") == "deadbeef"
}
