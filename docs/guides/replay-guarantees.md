# Replay guarantees

## Replay model

`pf evidence replay` consumes an Evidence v0.1 bundle, runs strict validation, and verifies execution-trace self-consistency. It is a **bundle-level audit step**, not a full TRACE-REPLAY-KIT or SWE-bench re-execution.

## Replayable claims

A bundle replay **may** establish:

- Bundle manifest schema conformance
- Artifact presence and byte-level digests
- `bundle_digest` integrity
- `trace_digest` self-consistency when an `execution-trace` artifact is present

## Non-replayable claims

Replay **does not** establish:

- End-to-end system determinism
- External API or model behavior reproducibility
- CERT signature validity (use CERT tooling)
- PCS science-claim admission
- Policy or proof correctness

## Determinism assumptions

- Canonical JSON digest rules in [`core/evidence/digest.go`](../../core/evidence/digest.go) are stable for a given input object
- Trace files on disk are unchanged between pack and replay
- Clock fields in reports (`replayed_at`) are not used for pass/fail

## External dependency assumptions

- `specs/evidence/v0.1/schemas/` present in the repository checkout
- Artifact paths resolve relative to bundle base directory
- TRACE-REPLAY-KIT is **not** invoked; traces are validated structurally only

## Input and fixture requirements

- Valid v0.1 bundle JSON
- For trace checks: one or more `execution-trace` role artifacts with valid `trace_digest`
- Strict mode requires all referenced artifact files to exist

## Report structure

Replay emits JSON with:

| Field | Meaning |
|-------|---------|
| `report_id` | Unique replay run identifier |
| `bundle_ref` | Input bundle path |
| `status` | `pass` or `fail` |
| `trace_found` | Whether an execution-trace artifact was present |
| `errors` | Machine-readable failure reasons |
| `warnings` | Non-fatal conditions (e.g. no trace artifact) |
| `replayed_at` | RFC3339 timestamp |

## Failure interpretation

| Failure | Meaning |
|---------|---------|
| Validation errors | Bundle schema, digest, or missing artifact |
| `trace_digest mismatch` | Trace JSON was tampered after digest computation |
| `no execution-trace artifact` | Warning only; partial replay preconditions |

A replay failure means **the bundle or trace failed v0.1 checks**, not necessarily that the original runtime execution was incorrect.

## Relation to runtime evidence

Runtime `evidence_v01_binding` events link certs to optional bundle refs. Replay does not read binding JSONL directly; package binding outputs into bundles first.

## Relation to Evidence v0.1 bundles

Replay operates only on v0.1 bundle manifests. It does not consume PCS `EvidenceBundle.v0` or `so bundle pack` tar archives.

## Known limitations

- Does not call `so trace run`
- Does not re-run SWE-bench instances
- Warnings when no trace artifact is present still yield `pass` if validation succeeds

## Related

- [Forensic replay basic](forensic-replay-basic.md)
- [Evidence replay tests](../../tests/evidence_replay/test_evidence_replay.py)
- [Evidence model v0.1](../specs/evidence-model-v0.1.md)
