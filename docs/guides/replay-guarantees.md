# Replay guarantees

## Replay model

`pf evidence replay` consumes an Evidence v0.1 or v0.2 bundle, runs strict validation, and verifies execution-trace self-consistency. With `--execute`, it also runs TRACE-REPLAY-KIT (`runner/replay_run.py`) using v0.2 `replay_context` or inferred fixture paths.

## Modes

| Mode | Flags | Guarantees |
|------|-------|------------|
| Static (default) | none | Schema, digests, `trace_digest`, optional `replay_context` path checks |
| Execute | `--execute` | Static checks plus KIT run exit code |
| Low-view | `--execute --low-view` | Two KIT runs + `oracles/lowview_equal.py` determinism check |

v0.1 bundles without `replay_context` continue to work in static mode only.

## Replayable claims

A bundle replay **may** establish:

- Bundle manifest schema conformance (v0.1 or v0.2)
- Artifact presence and byte-level digests
- `bundle_digest` integrity
- `trace_digest` self-consistency when an `execution-trace` artifact is present
- With `--execute`: KIT runner completed with exit code 0 for resolved trace/fixtures
- With `--low-view`: low-view oracle pass between two KIT outputs

## Non-replayable claims

Replay **does not** establish:

- CERT DSSE signature validity (use CERT tooling)
- PCS science-claim admission
- Policy or proof correctness
- Morph environment reproducibility
- PCS or spec-tar lane compatibility

## Determinism assumptions

- Canonical JSON digest rules in [`core/evidence/digest.go`](../../core/evidence/digest.go) are stable for a given input object
- Trace files on disk are unchanged between pack and replay
- KIT Python dependencies match `external/TRACE-REPLAY-KIT/runner/requirements.txt`
- Clock fields in reports (`replayed_at`) are not used for pass/fail

## External dependency assumptions

- `specs/evidence/v0.1/schemas/` (and v0.2 bundle schema when applicable) present in checkout
- `make submodules` for `--execute` / `--low-view`
- Artifact paths resolve relative to bundle base directory (`--base-dir`)

## Report structure (v0.2 fields)

| Field | Meaning |
|-------|---------|
| `status` | Overall `pass` or `fail` |
| `static_status` | Static validation + trace digest phase |
| `execute_status` | KIT run result when `--execute` |
| `kit_exit_code` | Process exit code from KIT runner |
| `low_view_result` | Low-view oracle result when requested |
| `trace_found` | Whether an execution-trace artifact was present |
| `errors` / `warnings` | Machine-readable messages |

## Failure interpretation

| Failure | Meaning |
|---------|---------|
| Static fail | Fix bundle, artifacts, or digests before execute |
| Execute fail | KIT trace/fixtures mismatch or runner error |
| Low-view fail | Non-deterministic outputs between two runs |

## Related commands

- `pf evidence trace import` — convert KIT trace JSON to v0.1 execution-trace artifact
- `so trace run` — direct KIT invocation without Evidence bundle coupling
