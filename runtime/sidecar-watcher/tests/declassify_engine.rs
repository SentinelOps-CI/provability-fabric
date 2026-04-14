/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

use sidecar_watcher::declassify::{
    DeclassBlock, DeclassEnforcer, DeclassRule, SecurityLabel,
};

fn make_rules() -> Vec<DeclassRule> {
    vec![
        DeclassRule {
            from_label: SecurityLabel::Secret,
            to_label: SecurityLabel::Confidential,
            conditions: vec!["business_need".to_string()],
            derivation: "rule_1".to_string(),
        },
        DeclassRule {
            from_label: SecurityLabel::Confidential,
            to_label: SecurityLabel::Public,
            conditions: vec!["public_release".to_string()],
            derivation: "rule_2".to_string(),
        },
    ]
}

#[test]
fn test_declassify_engine_basic() {
    let rules = make_rules();
    let block = DeclassBlock { rules };
    let enforcer = DeclassEnforcer::new(block).expect("well-formed block");

    let ok = enforcer
        .enforce_declass(
            &SecurityLabel::Secret,
            &SecurityLabel::Confidential,
            &["business_need".to_string()],
        )
        .expect("enforce_declass");
    assert!(ok);
}

#[test]
fn test_declassify_engine_widening_rejected() {
    let rules = make_rules();
    let block = DeclassBlock { rules };
    let enforcer = DeclassEnforcer::new(block).expect("well-formed block");

    assert!(enforcer.check_label_widening(
        &SecurityLabel::Confidential,
        &SecurityLabel::Secret
    ));
}

#[test]
fn test_declassify_engine_cycle_rejected() {
    let rules = vec![
        DeclassRule {
            from_label: SecurityLabel::Secret,
            to_label: SecurityLabel::Confidential,
            conditions: vec![],
            derivation: "a".to_string(),
        },
        DeclassRule {
            from_label: SecurityLabel::Confidential,
            to_label: SecurityLabel::Secret,
            conditions: vec![],
            derivation: "b".to_string(),
        },
    ];
    let block = DeclassBlock { rules };
    let res = DeclassEnforcer::new(block);
    assert!(res.is_err(), "cycle should be rejected");
}

#[test]
fn test_declassify_engine_widen_rule_rejected() {
    let rules = vec![DeclassRule {
        from_label: SecurityLabel::Public,
        to_label: SecurityLabel::Secret,
        conditions: vec![],
        derivation: "bad".to_string(),
    }];
    let block = DeclassBlock { rules };
    let res = DeclassEnforcer::new(block);
    assert!(res.is_err(), "widening rule should be rejected");
}
