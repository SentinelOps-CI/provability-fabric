// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use sidecar_watcher::env_config::{self, ENV_ENFORCE_DSSE};

fn clear_evidence_env() {
    for name in env_config::EVIDENCE_HASH_ENV_VARS {
        std::env::remove_var(name);
    }
    std::env::remove_var(env_config::EVIDENCE_RESOURCE_ID_ENV);
    std::env::remove_var(ENV_ENFORCE_DSSE);
}

#[test]
fn egress_evidence_denies_placeholder_policy_hash_when_enforced() {
    clear_evidence_env();
    std::env::set_var(ENV_ENFORCE_DSSE, "1");
    std::env::set_var("POLICY_HASH", "test-policy-hash");

    let err = env_config::resolve_evidence_hash("POLICY_HASH", "test-policy-hash")
        .expect_err("placeholder must be rejected");

    assert!(
        err.contains("rejecting placeholder"),
        "unexpected error: {err}"
    );

    clear_evidence_env();
}

#[test]
fn egress_evidence_denies_missing_hashes_when_enforced() {
    clear_evidence_env();
    std::env::set_var(ENV_ENFORCE_DSSE, "1");

    let err = env_config::resolve_evidence_hash("PLAN_HASH", "test-plan-hash")
        .expect_err("missing hash must be rejected");

    assert!(err.contains("missing PLAN_HASH"), "unexpected error: {err}");

    clear_evidence_env();
}
