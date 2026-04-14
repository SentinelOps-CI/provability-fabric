# OpenHands Compatibility Matrix (Runtime + Prime/OpenAI)

This document captures the runtime expectations of the SWE-bench OpenHands integration in this repository.
It is intended to be used when selecting/pinning OpenHands versions and when debugging Prime/OpenAI provider behavior.

## Capability probe (what the engine detects)

At runtime, `bench/swebench/engines/openhands_engine.py` probes whether the installed `openhands` package exposes the library entrypoint:

- `openhands.core.main` importable
- If not importable, the engine is treated as CLI-only and forced onto the `openhands` subprocess path.

The per-run capability and the selected execution mode are written into:

- `workspaces/<id>/env.json` (provider + model routing + `openhands_package_capabilities`)
- `workspaces/<id>/<instance>/engine_trace.json` (execution/capability metadata)

## Execution mode selection

Given `OPENHANDS_PROVIDER`:

- `prime_intellect`
  - Expected execution mode: `prime_subprocess`
  - The engine uses the local Prime strict-compat proxy (payload normalization for tool-call messages).
- Any other provider (e.g. `openai`, `anthropic`)
  - If `openhands.core.main` is importable: `library`
  - Otherwise: `cli_subprocess`

## Prime strict-compat proxy contract

When `OPENHANDS_PROVIDER=prime_intellect`, the engine routes requests through a local proxy that normalizes OpenAI-compatible payload shapes expected by strict servers.
The proxy applies (at minimum) this transformation for assistant tool-call messages:

- If an assistant message contains `tool_calls` but is missing `content` (or has `content=None`), the proxy sets `content=""`.

The engine exposes compatibility health counters in `engine_trace.json`:

- `prime_proxy_enabled`
- `prime_payload_normalizations_applied`
- `prime_422_avoided`

If `prime_422_avoided < prime_payload_normalizations_applied` while `prime_payload_normalizations_applied > 0`, this indicates upstream 422s still occurred and the compat normalization did not fully prevent the strict-schema rejection.

## Prompt truncation and fidelity guarantees

The engine uses deterministic prompt compaction to reduce prompt length while preserving critical blocks from the SWE-bench task prompt.

Controls:

- `PF_OPENHANDS_MAX_TASK_CHARS` (default is conservative)

Diagnostics:

- `engine_trace.json` includes `task_delivery_report`:
  - `compaction_applied`
  - `critical_drop` (true means required blocks may have been dropped by compaction)
  - `sidecar_path` (location of the full task prompt stored for debugging)

## Pin strategy (practical guidance)

When updating/pinning OpenHands:

1. Verify the installed `openhands` executable and python package version match expectations.
2. Run:
   - `python experiments/scripts/openhands_regression_gate.py --provider <openai|prime_intellect|anthropic> --timeout 180 --max-iterations 2`
   - The gate defaults to a large enough `PF_OPENHANDS_MAX_TASK_CHARS` (unless you override) so its long synthetic prompt is not flagged as `critical_drop`. For full SWE-bench runs you may still tune `PF_OPENHANDS_MAX_TASK_CHARS` separately.
3. Inspect:
   - `engine_trace.json` for execution mode, timeout attribution, `task_delivery_report.critical_drop`, and Prime proxy counters.

## Probe and gate scripts

### Direct CLI probe (runtime/provider comparison)

`experiments/scripts/openhands_cli_probe.py`

Runs `openhands` directly (no engine proxy/wiring) and emits a JSON summary including event-derived latency metrics.

### Operational regression gate (stabilization invariants)

`experiments/scripts/openhands_regression_gate.py`

Runs a single synthetic solve via the repository engine and fails if any stabilization invariants are violated.

