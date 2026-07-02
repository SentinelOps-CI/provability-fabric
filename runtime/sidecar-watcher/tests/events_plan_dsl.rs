/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

use sidecar_watcher::events::{EventMediator, EventType, PlanNode, TypedEvent};
use std::collections::HashMap;

#[test]
fn test_event_mediator_matches_plan_node() {
    let mut mediator = EventMediator::new(vec![EventType::Call], true);

    let mut args = HashMap::new();
    args.insert("param".to_string(), serde_json::json!("value"));
    let event = TypedEvent::new(
        EventType::Call,
        args,
        vec!["input".to_string()],
        vec!["output".to_string()],
        vec!["cap1".to_string()],
        "session123".to_string(),
        "plan_hash".to_string(),
    )
    .unwrap();

    let plan_node = PlanNode {
        operation: EventType::Call,
        field_commit: event.field_commit().to_string(),
        args_hash: event.args_hash().to_string(),
        caps_required: vec!["cap1".to_string()],
        labels_in: vec!["input".to_string()],
        labels_out: vec!["output".to_string()],
    };
    mediator.add_plan_node("node1".to_string(), plan_node);

    assert!(mediator.mediate_event(&event).is_ok());
}

#[test]
fn test_event_mediator_rejects_unknown_operation() {
    let mediator = EventMediator::new(vec![EventType::Log], true);
    let event = TypedEvent::new(
        EventType::Call,
        HashMap::new(),
        vec![],
        vec![],
        vec![],
        "session123".to_string(),
        "plan_hash".to_string(),
    )
    .unwrap();
    assert!(mediator.mediate_event(&event).is_err());
}
