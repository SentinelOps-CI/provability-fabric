# Sidecar / admission audit line → PF-Core runtime_observation.v1

Phase 7 PR-4 field mapping. Admission-controller and sidecar-watcher emit the same audit JSON shape; native emission replaces the provability-fabric-core normalize shim.

## Sidecar audit field → PF-Core v1

| Audit field | PF-Core v1 field |
|-------------|------------------|
| `request_id` | `observation_id` |
| `trace_id` | `trace_id` |
| `event_id` | `event_id` |
| `agent_id` | `principal.id` |
| `tenant` | `principal.tenant_id` |
| `tool_effect` | `action.effects[].kind` |
| `resource` | `action.reads[].uri` |
| `policy_decision` | `decision` |
| `prev_hash` | `previous_event_hash` |
| `policy_bundle` | `policy_ref` |
| `audit_bundle` | `evidence_ref` |
| `capability_hint` | `action.capability.id` |
| `runtime_ref` | `runtime_ref` |
| `timestamp` | `timestamp` |
| `reason` | `reason` |

Principal roles resolve from `fixtures/capability_catalog.json` (`principal_roles_by_capability`), not hardcoded.

## Native emission

```bash
cat tests/fixtures/sidecar_audit_line.json | cargo run --bin emit_observation
pf core compile-observation --schemas vendor/pf-core/schemas --file obs.json
```

## Parity gate

```bash
bash scripts/test_admission_parity.sh
```

Compares native Rust output to reference `adapters/provability-fabric/mcp_sidecar/normalize.py` on golden fixtures.
