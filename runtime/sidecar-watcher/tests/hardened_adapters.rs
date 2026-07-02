/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

use sidecar_watcher::effects::{EffectSignature, EffectType, EffectsAllowList};

#[test]
fn test_http_get_adapter_hardening() {
    let mut allow_list = EffectsAllowList::new();
    let effect = EffectSignature::new(EffectType::HttpGet, "https://example.com/api".to_string());
    assert!(allow_list.allow_effect(effect).is_ok());
    assert!(allow_list.is_effect_allowed(&EffectType::HttpGet, "https://example.com/api"));
    assert!(!allow_list.is_effect_allowed(
        &EffectType::HttpGet,
        "https://evil.example/redirect"
    ));
}

#[test]
fn test_file_read_adapter_hardening() {
    let mut allow_list = EffectsAllowList::new();
    let effect = EffectSignature::new(EffectType::FileRead, "/var/data/readme.txt".to_string());
    assert!(allow_list.allow_effect(effect).is_ok());
    assert!(allow_list.is_effect_allowed(&EffectType::FileRead, "/var/data/readme.txt"));
    assert!(!allow_list.is_effect_allowed(&EffectType::FileRead, "/etc/passwd"));
}

#[test]
fn test_get_allowed_effects_lists_registered_signatures() {
    let mut allow_list = EffectsAllowList::new();
    allow_list
        .allow_effect(EffectSignature::new(
            EffectType::HttpGet,
            "https://example.com".to_string(),
        ))
        .unwrap();
    assert_eq!(allow_list.get_allowed_effects().len(), 1);
}
