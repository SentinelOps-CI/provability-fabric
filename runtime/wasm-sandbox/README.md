# WASM Sandbox

WebAssembly sandbox for third-party adapters. Runs WASM modules with fuel limits, optional module-hash verification, and an in-process instance pool. Built on wasmtime 15 with WASI support.

## Current implementation

- **CLI binary**: Loads a single WASM module, verifies its hash (optional), runs it with optional input, and prints a JSON verification result.
- **Instance pool**: Internally maintains a pool of WASM instances per module (keyed by SHA256 of the module). Instances are reused and health-checked; unhealthy instances are replaced.
- **Fuel**: Execution is limited by a configurable fuel budget (default 1,000,000).
- **WASI**: Uses wasmtime-wasi (WasiCtx / WasiCtxBuilder) for WASI preview1-style host bindings. Network and filesystem are disabled by default; `--allow-network` and `--allow-fs` are reserved for future use.

## Prerequisites

- Rust (edition 2021) and Cargo
- Build from workspace root: `cargo build -p wasm-sandbox`

## Usage

```bash
# From repository root
cargo run -p wasm-sandbox -- --module path/to/module.wasm

# With optional hash verification and input
cargo run -p wasm-sandbox -- \
  --module path/to/module.wasm \
  --expected-hash <sha256-hex> \
  --fuel-limit 2000000 \
  --input '{"key":"value"}'
```

### CLI options

| Option | Short | Default | Description |
|--------|-------|---------|-------------|
| `--module` | `-m` | (required) | Path to the WebAssembly module (.wasm) |
| `--expected-hash` | `-e` | none | If set, module is verified against this SHA256 (hex) before execution |
| `--fuel-limit` | `-f` | 1000000 | Maximum fuel units for execution |
| `--allow-network` | | false | Reserved; network access remains disabled |
| `--allow-fs` | | false | Reserved; filesystem access remains disabled |
| `--input` | `-i` | none | Optional JSON string passed as input to the module |

### Output

The program prints a JSON object to stdout:

- `success`: boolean
- `witness`: optional JSON value (execution witness)
- `error`: optional string (if failed)
- `fuel_consumed`: number
- `execution_time_ms`: number

On failure, the process exits with a non-zero code.

## Architecture (current)

- **WasmSandbox**: Holds the wasmtime `Engine` and an `InstancePool`. Entry point for `execute_module` and `compute_module_hash`.
- **InstancePool**: Maps module hash to a list of `PooledInstance`s. `get_instance` returns a healthy instance or creates one; `return_instance` returns it to the pool or replaces unhealthy instances. A background task runs health checks.
- **Security**: Optional hash verification; `scan_for_prohibited_ops` checks module imports against policy: when `--allow-fs` is false, path/fd WASI imports are prohibited; when `--allow-network` is false, socket imports are prohibited. Fuel limits and WASI capabilities are enforced by the runtime.

## Building and testing

```bash
cargo build -p wasm-sandbox
cargo test -p wasm-sandbox
```

## Planned / future

- Full WASI integration (preopened dirs, args, env) when `--allow-fs` or network is enabled.
- Public library API (e.g. pool-based execution) for embedding in other services; current code is CLI-only.
