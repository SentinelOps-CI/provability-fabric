# WASM Sandbox

Restricted, single-command execution of binary core WebAssembly with Wasmtime
36.0.22. This interface replaces the previous mocked execution result and
invalid instance-pool ownership model. It does not implement a proof verifier.

## Supported contract

- The guest must be a binary core WebAssembly module exporting `_start: () -> ()`.
- All imports are rejected, including WASI, before instantiation. No host
  filesystem, network, environment, or standard streams are exposed.
- Each invocation uses a fresh store and instance. The fuel budget applies to
  instantiation (including a start section) and the exported entrypoint.
- The module is read once with a 16 MiB size limit, then optionally checked
  against a SHA256 digest and compiled from that same byte buffer.
- The store limits guest linear memory to 64 MiB, table size to 10,000 elements,
  and the number of memories, tables and instances to one each. Failed growth
  traps. These limits do not bound all compiler or host resource consumption.
- A normal return reports execution success with measured fuel and elapsed
  execution time; a trap or entrypoint error reports failure. No proof witness
  is fabricated. Invalid inputs and compilation failures return nonzero.

## Usage

```bash
cargo build --locked -p wasm-sandbox
cargo run --locked -p wasm-sandbox -- --module command.wasm --fuel-limit 1000000
```

Optional `--expected-hash` verifies the exact module bytes. The legacy
`--allow-network`, `--allow-fs`, and `--input` options are rejected explicitly;
WASI, guest input ABI and pooling are unsupported. This is an intentional
compatibility restriction pending independently validated capability interfaces.

## Validation

```bash
cargo test --locked -p wasm-sandbox
```

The regression suite checks actual entrypoint execution, traps, fuel exhaustion
during instantiation and execution, import rejection, entrypoint signatures,
linear-memory bounds, hash binding and unsupported options. Fuel is a Wasmtime
execution budget, not a wall-clock deadline. Run untrusted workloads under
independent OS-level CPU, memory and time limits. The CLI is not a general-purpose
untrusted-code service or a verified isolation boundary.
