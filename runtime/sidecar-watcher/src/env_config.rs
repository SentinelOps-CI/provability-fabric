// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use std::env;

pub const ENV_ENFORCE_DSSE: &str = "PF_ENFORCE_DSSE";
pub const ENV_SHADOW_MODE: &str = "PF_SHADOW_MODE";
pub const ENV_TRUST_ROOT_PEM: &str = "PF_TRUST_ROOT_PEM";
pub const ENV_PROFILE: &str = "PF_PROFILE";
pub const ENV_ENABLED_TOOLS: &str = "PF_ENABLED_TOOLS";

/// Fail-closed by default; opt out only with `PF_ENFORCE_DSSE=0` or `false`.
pub fn enforce_dsse() -> bool {
    match env::var(ENV_ENFORCE_DSSE) {
        Ok(v) => {
            let v = v.trim();
            !(v == "0" || v.eq_ignore_ascii_case("false"))
        }
        Err(_) => true,
    }
}

/// Shadow bypass is dev-only: requires PF_SHADOW_MODE=1 and non-production profile.
pub fn shadow_mode_allowed() -> bool {
    if !env_flag(ENV_SHADOW_MODE) {
        return false;
    }
    !is_production_profile()
}

pub fn is_production_profile() -> bool {
    matches!(
        env::var(ENV_PROFILE)
            .unwrap_or_default()
            .to_ascii_lowercase()
            .as_str(),
        "production" | "prod"
    )
}

pub fn env_flag(name: &str) -> bool {
    match env::var(name) {
        Ok(v) => v == "1" || v.eq_ignore_ascii_case("true"),
        Err(_) => false,
    }
}

pub fn enabled_tools_override() -> Vec<String> {
    env::var(ENV_ENABLED_TOOLS)
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Env vars that must be set to non-placeholder values when DSSE enforcement is active.
pub const EVIDENCE_HASH_ENV_VARS: &[&str] = &[
    "PLAN_HASH",
    "POLICY_HASH",
    "AUTOMATA_HASH",
    "LABELER_HASH",
    "NI_MONITOR_HASH",
];

pub const EVIDENCE_RESOURCE_ID_ENV: &str = "RESOURCE_ID";

pub fn is_placeholder_evidence_value(value: &str) -> bool {
    let trimmed = value.trim();
    trimmed.is_empty() || trimmed.starts_with("test-")
}

/// True when egress cert evidence must not use dev fallbacks.
pub fn evidence_hash_enforced() -> bool {
    enforce_dsse() || is_production_profile()
}

/// Resolve an evidence hash env var, rejecting missing/placeholder values when enforced.
pub fn resolve_evidence_hash(name: &str, dev_default: &str) -> Result<String, String> {
    let raw = match env::var(name) {
        Ok(v) => v,
        Err(_) if evidence_hash_enforced() => {
            return Err(format!(
                "missing {name} when DSSE enforcement is active or production profile"
            ));
        }
        Err(_) => {
            tracing::warn!(
                env = name,
                default = dev_default,
                "using dev fallback for evidence hash"
            );
            return Ok(dev_default.to_string());
        }
    };

    if evidence_hash_enforced() && is_placeholder_evidence_value(&raw) {
        return Err(format!(
            "rejecting placeholder {name}={raw:?} when DSSE enforcement is active or production profile"
        ));
    }

    Ok(raw)
}

#[cfg(test)]
mod evidence_hash_tests {
    use super::*;
    use std::sync::{Mutex, MutexGuard};

    static ENV_TEST_LOCK: Mutex<()> = Mutex::new(());

    fn env_test_guard() -> MutexGuard<'static, ()> {
        ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn clear_evidence_env() {
        for name in EVIDENCE_HASH_ENV_VARS {
            env::remove_var(name);
        }
        env::remove_var(EVIDENCE_RESOURCE_ID_ENV);
        env::remove_var(ENV_ENFORCE_DSSE);
        env::remove_var(ENV_PROFILE);
    }

    #[test]
    fn allows_dev_fallback_when_not_enforced() {
        let _guard = env_test_guard();
        clear_evidence_env();
        env::set_var(ENV_ENFORCE_DSSE, "0");
        let value = resolve_evidence_hash("POLICY_HASH", "test-policy-hash").expect("dev fallback");
        assert_eq!(value, "test-policy-hash");
        clear_evidence_env();
    }

    #[test]
    fn rejects_missing_hash_when_unset_defaults_to_enforce() {
        let _guard = env_test_guard();
        clear_evidence_env();
        // Unset PF_ENFORCE_DSSE → fail-closed (enforce).
        let err = resolve_evidence_hash("POLICY_HASH", "test-policy-hash").unwrap_err();
        assert!(err.contains("missing POLICY_HASH"));
        clear_evidence_env();
    }

    #[test]
    fn rejects_missing_hash_when_enforced() {
        let _guard = env_test_guard();
        clear_evidence_env();
        env::set_var(ENV_ENFORCE_DSSE, "1");
        let err = resolve_evidence_hash("POLICY_HASH", "test-policy-hash").unwrap_err();
        assert!(err.contains("missing POLICY_HASH"));
        clear_evidence_env();
    }

    #[test]
    fn rejects_placeholder_hash_when_enforced() {
        let _guard = env_test_guard();
        clear_evidence_env();
        env::set_var(ENV_ENFORCE_DSSE, "1");
        env::set_var("POLICY_HASH", "test-policy-hash");
        let err = resolve_evidence_hash("POLICY_HASH", "test-policy-hash").unwrap_err();
        assert!(err.contains("rejecting placeholder"));
        clear_evidence_env();
    }

    #[test]
    fn accepts_real_hash_when_enforced() {
        let _guard = env_test_guard();
        clear_evidence_env();
        env::set_var(ENV_ENFORCE_DSSE, "1");
        env::set_var(
            "POLICY_HASH",
            "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        );
        let value = resolve_evidence_hash("POLICY_HASH", "test-policy-hash").expect("real hash");
        assert!(value.starts_with("sha256:"));
        clear_evidence_env();
    }

    #[test]
    fn enabled_tools_deny_by_default() {
        let _guard = env_test_guard();
        env::remove_var(ENV_ENABLED_TOOLS);
        assert!(enabled_tools_override().is_empty());
        env::set_var(ENV_ENABLED_TOOLS, "");
        assert!(enabled_tools_override().is_empty());
        env::set_var(ENV_ENABLED_TOOLS, "retrieve, send_email");
        let tools = enabled_tools_override();
        assert_eq!(tools, vec!["retrieve", "send_email"]);
        env::remove_var(ENV_ENABLED_TOOLS);
    }
}
