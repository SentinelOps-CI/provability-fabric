// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! Native emission of `pf-core.runtime_observation.v1` from sidecar audit lines.

use anyhow::{anyhow, Context, Result};
use serde::Deserialize;
use serde_json::{Map, Value};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

const GENESIS_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";
const PLACEHOLDER_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";

#[derive(Debug, Clone, Deserialize)]
pub struct SidecarAuditLine {
    pub request_id: Option<String>,
    pub trace_id: Option<String>,
    pub event_id: Option<String>,
    pub agent_id: Option<String>,
    pub tenant: Option<String>,
    pub tool_effect: Option<String>,
    pub resource: Option<String>,
    pub policy_decision: Option<String>,
    pub prev_hash: Option<String>,
    pub policy_bundle: Option<String>,
    pub audit_bundle: Option<String>,
    pub capability_hint: Option<String>,
    pub runtime_ref: Option<String>,
    pub timestamp: Option<String>,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct CapabilityCatalog {
    capabilities: Vec<CapabilityEntry>,
    principal_roles_by_capability: HashMap<String, Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
struct CapabilityEntry {
    id: String,
    effect_kind: String,
    resource_pattern: String,
}

fn load_catalog(path: &Path) -> Result<CapabilityCatalog> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("read capability catalog {}", path.display()))?;
    serde_json::from_str(&text).context("parse capability catalog")
}

fn map_decision(raw: &str) -> String {
    match raw.to_ascii_lowercase().as_str() {
        "allow" | "allowed" | "permit" | "permitted" => "allowed".to_string(),
        "deny" | "denied" | "block" | "blocked" => "denied".to_string(),
        other => other.to_string(),
    }
}

fn resolve_capability_id(
    catalog: &CapabilityCatalog,
    effect_kind: &str,
    hint: Option<&str>,
) -> Result<String> {
    let matches: Vec<_> = catalog
        .capabilities
        .iter()
        .filter(|c| c.effect_kind == effect_kind)
        .collect();
    if let Some(id) = hint {
        return Ok(id.to_string());
    }
    if matches.len() == 1 {
        return Ok(matches[0].id.clone());
    }
    if matches.len() > 1 {
        let ids: Vec<_> = matches.iter().map(|c| c.id.as_str()).collect();
        return Err(anyhow!(
            "capability_hint required for effect {effect_kind}; matches {ids:?}"
        ));
    }
    Err(anyhow!("no catalog capability for effect {effect_kind}"))
}

fn resource_pattern_for(catalog: &CapabilityCatalog, capability_id: &str) -> String {
    catalog
        .capabilities
        .iter()
        .find(|c| c.id == capability_id)
        .map(|c| c.resource_pattern.clone())
        .unwrap_or_else(|| "mcp:*".to_string())
}

fn roles_for_capability(catalog: &CapabilityCatalog, capability_id: &str) -> Vec<String> {
    catalog
        .principal_roles_by_capability
        .get(capability_id)
        .cloned()
        .filter(|roles| !roles.is_empty())
        .unwrap_or_else(|| vec!["mcp_user".to_string()])
}

fn string_field(obj: &mut Map<String, Value>, key: &str, value: String) {
    obj.insert(key.to_string(), Value::String(value));
}

fn principal_object(
    principal_id: &str,
    tenant_id: &str,
    roles: &[String],
    capability_id: &str,
) -> Value {
    let mut obj = Map::new();
    string_field(&mut obj, "schema_version", "pf-core.principal.v1".to_string());
    string_field(&mut obj, "id", principal_id.to_string());
    string_field(&mut obj, "tenant_id", tenant_id.to_string());
    obj.insert(
        "roles".to_string(),
        Value::Array(roles.iter().cloned().map(Value::String).collect()),
    );
    obj.insert(
        "capabilities".to_string(),
        Value::Array(vec![Value::String(capability_id.to_string())]),
    );
    Value::Object(obj)
}

/// Map a sidecar audit line to `pf-core.runtime_observation.v1`.
pub(crate) fn emit_runtime_observation(
    line: &SidecarAuditLine,
    catalog: &CapabilityCatalog,
) -> Result<Value> {
    let observation_id = line
        .request_id
        .clone()
        .or_else(|| line.event_id.clone())
        .unwrap_or_else(|| "obs-unknown".to_string());
    let trace_id = line
        .trace_id
        .clone()
        .unwrap_or_else(|| format!("trace-{observation_id}"));
    let event_id = line
        .event_id
        .clone()
        .unwrap_or_else(|| observation_id.clone());
    let principal_id = line
        .agent_id
        .clone()
        .unwrap_or_else(|| "unknown-agent".to_string());
    let tenant_id = line
        .tenant
        .clone()
        .unwrap_or_else(|| "unknown-tenant".to_string());
    let effect_kind = line
        .tool_effect
        .clone()
        .unwrap_or_else(|| "mcp.invoke".to_string());
    let resource_uri = line
        .resource
        .clone()
        .unwrap_or_else(|| "mcp:unknown".to_string());
    let decision = map_decision(
        line.policy_decision
            .as_deref()
            .unwrap_or("denied"),
    );
    let prev_hash = line
        .prev_hash
        .clone()
        .unwrap_or_else(|| GENESIS_HASH.to_string());

    let capability_id = resolve_capability_id(
        catalog,
        &effect_kind,
        line.capability_hint.as_deref(),
    )?;
    let roles = roles_for_capability(catalog, &capability_id);

    let principal = principal_object(&principal_id, &tenant_id, &roles, &capability_id);

    let mut capability = Map::new();
    string_field(&mut capability, "schema_version", "pf-core.capability.v0".to_string());
    string_field(&mut capability, "id", capability_id.clone());
    string_field(&mut capability, "effect_kind", effect_kind.clone());
    string_field(&mut capability, "resource_pattern", resource_pattern_for(catalog, &capability_id));

    let mut effect = Map::new();
    string_field(&mut effect, "schema_version", "pf-core.effect.v0".to_string());
    string_field(&mut effect, "kind", effect_kind.clone());

    let mut read_resource = Map::new();
    string_field(
        &mut read_resource,
        "schema_version",
        "pf-core.resource.v0".to_string(),
    );
    string_field(&mut read_resource, "uri", resource_uri);
    string_field(&mut read_resource, "tenant_id", tenant_id.clone());

    let mut action = Map::new();
    string_field(&mut action, "schema_version", "pf-core.action.v1".to_string());
    string_field(&mut action, "id", format!("act-{observation_id}"));
    action.insert("principal".to_string(), principal.clone());
    action.insert("capability".to_string(), Value::Object(capability));
    action.insert(
        "effects".to_string(),
        Value::Array(vec![Value::Object(effect)]),
    );
    action.insert(
        "reads".to_string(),
        Value::Array(vec![Value::Object(read_resource)]),
    );
    action.insert("writes".to_string(), Value::Array(vec![]));

    let mut obs = Map::new();
    string_field(
        &mut obs,
        "schema_version",
        "pf-core.runtime_observation.v1".to_string(),
    );
    string_field(&mut obs, "trace_id", trace_id);
    string_field(&mut obs, "event_id", event_id);
    string_field(&mut obs, "observation_id", observation_id);
    obs.insert("principal".to_string(), principal);
    obs.insert("action".to_string(), Value::Object(action));
    string_field(&mut obs, "decision", decision);
    string_field(
        &mut obs,
        "reason",
        line.reason
            .clone()
            .unwrap_or_else(|| "sidecar audit line".to_string()),
    );
    string_field(
        &mut obs,
        "policy_ref",
        line.policy_bundle
            .clone()
            .unwrap_or_else(|| "policy/default.v0".to_string()),
    );
    string_field(
        &mut obs,
        "evidence_ref",
        line.audit_bundle
            .clone()
            .unwrap_or_else(|| "evidence/mcp-audit.v0".to_string()),
    );
    string_field(
        &mut obs,
        "runtime_ref",
        line.runtime_ref
            .clone()
            .unwrap_or_else(|| "provability-fabric/sidecar-watcher".to_string()),
    );
    string_field(
        &mut obs,
        "timestamp",
        line.timestamp
            .clone()
            .unwrap_or_else(|| "2026-06-18T00:00:00Z".to_string()),
    );
    string_field(&mut obs, "previous_event_hash", prev_hash);
    string_field(&mut obs, "hash", PLACEHOLDER_HASH.to_string());

    Ok(Value::Object(obs))
}

pub fn default_catalog_path() -> &'static Path {
    Path::new("fixtures/capability_catalog.json")
}

pub fn emit_from_audit_json(line_json: &str, catalog_path: &Path) -> Result<Value> {
    let line: SidecarAuditLine = serde_json::from_str(line_json)?;
    let catalog = load_catalog(catalog_path)?;
    emit_runtime_observation(&line, &catalog)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn fixture_path(name: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(name)
    }

    fn catalog_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/capability_catalog.json")
    }

    #[test]
    fn golden_allowed_line_matches_semantics() {
        let text = fs::read_to_string(fixture_path("sidecar_audit_line.json")).unwrap();
        let line: SidecarAuditLine = serde_json::from_str(&text).unwrap();
        let catalog = load_catalog(&catalog_path()).unwrap();
        let obs = emit_runtime_observation(&line, &catalog).unwrap();
        assert_eq!(
            obs.get("schema_version").and_then(Value::as_str),
            Some("pf-core.runtime_observation.v1")
        );
        assert_eq!(obs.get("decision").and_then(Value::as_str), Some("allowed"));
        let roles = obs["principal"]["roles"].as_array().unwrap();
        assert_eq!(roles.len(), 2);
        assert_eq!(roles[0], "mcp_user");
        assert_eq!(roles[1], "agent");
    }

    #[test]
    fn denied_line_maps_decision() {
        let text = fs::read_to_string(fixture_path("sidecar_denied_audit_line.json")).unwrap();
        let line: SidecarAuditLine = serde_json::from_str(&text).unwrap();
        let catalog = load_catalog(&catalog_path()).unwrap();
        let obs = emit_runtime_observation(&line, &catalog).unwrap();
        assert_eq!(obs.get("decision").and_then(Value::as_str), Some("denied"));
    }

    #[test]
    fn missing_capability_hint_is_error() {
        let text =
            fs::read_to_string(fixture_path("sidecar_ambiguous_audit_line.json")).unwrap();
        let line: SidecarAuditLine = serde_json::from_str(&text).unwrap();
        let catalog = load_catalog(&catalog_path()).unwrap();
        let err = emit_runtime_observation(&line, &catalog).unwrap_err();
        assert!(err.to_string().contains("capability_hint required"));
    }
}
