# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

package provability

# Test case: Allow valid signature
test_allow_valid_signature {
    input := {
        "request": {
            "kind": {
                "kind": "Pod"
            },
            "object": {
                "metadata": {
                    "annotations": {
                        "spec.sig": "valid_signature_here"
                    }
                }
            }
        }
    }
    
    # Mock io.jwt.verify to return true for valid signatures
    io.jwt.verify("sigstore", "valid_signature_here") == true
    
    allow with input as input
}

# Test case: Deny revoked signature
test_deny_revoked_signature {
    input := {
        "request": {
            "kind": {
                "kind": "Pod"
            },
            "object": {
                "metadata": {
                    "annotations": {
                        "spec.sig": "revoked:some_signature"
                    }
                }
            }
        }
    }
    
    # Mock io.jwt.verify to return true (signature is valid)
    io.jwt.verify("sigstore", "revoked:some_signature") == true
    
    not allow with input as input
}

# Test case: Deny invalid signature
test_deny_invalid_signature {
    input := {
        "request": {
            "kind": {
                "kind": "Pod"
            },
            "object": {
                "metadata": {
                    "annotations": {
                        "spec.sig": "invalid_signature"
                    }
                }
            }
        }
    }
    
    # Mock io.jwt.verify to return false for invalid signatures
    io.jwt.verify("sigstore", "invalid_signature") == false
    
    not allow with input as input
}

# Test case: Deny missing spec.sig annotation
test_deny_missing_spec_sig {
    input := {
        "request": {
            "kind": {
                "kind": "Pod"
            },
            "object": {
                "metadata": {
                    "annotations": {}
                }
            }
        }
    }
    
    not allow with input as input
}

# Test case: Deny non-Pod resource
test_deny_non_pod_resource {
    input := {
        "request": {
            "kind": {
                "kind": "Service"
            },
            "object": {
                "metadata": {
                    "annotations": {
                        "spec.sig": "valid_signature"
                    }
                }
            }
        }
    }
    
    not allow with input as input
}

# Test revoked_signer function
test_revoked_signer_true {
    revoked_signer("revoked:some_signature")
}

test_revoked_signer_false {
    not revoked_signer("valid_signature")
}