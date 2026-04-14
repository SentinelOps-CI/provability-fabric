# Extension Points

This document describes how to extend Provability-Fabric with custom adapters, bundle templates, and runtime components. It is intended for maintainers of forks and for contributors adding new capabilities without changing core behavior.

## Adapters

Adapters live under the repository root `adapters/` directory. There are three categories: solver adapters (verification engines), I/O adapters (Rust crates for HTTP/file with policy integration), and middleware (framework-specific cert/policy hooks).

### Solver adapters

Solver adapters run verification engines (neural network or hybrid system) and produce proof artifacts. They are invoked as **scripts or CLIs** (often Python), not as long-running services.

| Adapter | Location | Invocation | Inputs | Outputs |
|---------|----------|------------|--------|---------|
| Marabou | `adapters/marabou/` | Python script (`adapter.py`) | Model file, property file | Proof / UNSAT or counter-example |
| DryVR | `adapters/dryvr/` | Shell script (`adapter.sh`) | Model, scenario, spec | Reach set / proof artifact |
| alpha-beta-crown | `adapters/alpha-beta-crown/` | Python (`adapter.py`, CLI) | Model path, property path, output dir | Verification result, bounds, proof |

**Contract for adding a new solver adapter:**

1. Add a directory `adapters/<name>/` with at least an entry point (e.g. `adapter.py` or `adapter.sh`).
2. **Inputs**: Accept model (or network) and property (or scenario) as files or paths; optionally timeout and device (CPU/GPU). Configuration can be via CLI args, env, or a small config file.
3. **Outputs**: Produce a deterministic artifact (proof, reach set, or verification result) that the platform can hash and attach to a bundle. Exit code or structured output (e.g. JSON) should indicate success/failure/timeout.
4. **Discovery**: The platform or spec references the adapter by name or path. Document the adapter in your fork and, if contributing upstream, add it to the adapters overview ([Adapters overview](../adapters/overview.md)) and any platform config that enumerates solvers.

No dynamic plugin loader is used; add your directory under `adapters/` and reference it from specs or build/config.

### I/O adapters (Rust)

I/O adapters are Rust crates that implement resource mapping, witness validation, and policy integration for concrete I/O (e.g. HTTP GET, file read). They are used by the runtime/sidecar and policy evaluation.

| Adapter | Crate | Purpose |
|---------|-------|---------|
| httpget | `adapters/http-get` (`httpget-adapter`) | HTTP GET with resource mapping, witness validation, IFC |
| fileread | `adapters/file-read` (`fileread-adapter`) | File read with path rules, witness validation, IFC |

**Contract for adding a new I/O adapter:**

1. Add a new crate under `adapters/<name>/` with `Cargo.toml` and implement the same patterns as httpget/fileread: effect signature (allowed operations, limits), resource mapping (doc id, field path, label), witness validation (Merkle path, signature), and policy/IFC integration.
2. Add the crate to the root workspace in `Cargo.toml`: `members = [ ..., "adapters/<name>" ]`.
3. Build and test from repo root: `cargo build -p <crate-name>`, `cargo test -p <crate-name>`.
4. Document how the sidecar or platform invokes it (e.g. config or policy that references the adapter). See [Adapters overview](../adapters/overview.md) for the unified permission model.

### Middleware (Express, FastAPI, Go chi)

Middleware adapters integrate with your application framework to emit CERT-V1-style certificates or enforce policy at the request level.

| Adapter | Location | Role |
|---------|----------|------|
| express-cert-middleware | `adapters/express-cert-middleware/` | Express (Node): CERT payload, optional signing |
| fastapi_cert_middleware | `adapters/fastapi_cert_middleware/` | FastAPI (Python): cert middleware |
| gochi-cert-middleware | `adapters/gochi-cert-middleware/` | Go chi: cert middleware |

**Contract for adding new middleware:**

1. Add `adapters/<name>/` with the middleware implementation. It should read policy/bundle hashes (e.g. from env: `CERT_POLICY_HASH`, `CERT_AUTOMATA_HASH`, `CERT_LABELER_HASH`) and attach them to the request/response or emit a CERT payload.
2. Follow the same shape as existing middleware: tenant id, session id, timestamp, method, path, latency, and hashes from the bundle manifest ([bundle-manifest-v1](../schemas/bundle-manifest-v1.json)).
3. Document how to mount the middleware in your framework and which env vars or config it expects.

## Bundles

### Bundle manifest (v1)

The platform and sidecar expect a bundle manifest with the following schema: [bundle-manifest-v1.json](../schemas/bundle-manifest-v1.json).

- **Required**: `version` (must be `"1"`), `policy_hash`, `automata_hash`, `labeler_hash` (SHA-256 hex).
- **Optional**: `bundle_hash` (hash of bundle file bytes).

When you add or build bundles, ensure the built artifact (or the sidecar/middleware config) provides these hashes so that verification and CERT emission stay consistent.

### Spec template layout (v1)

The default template lives at `spec-templates/v1/` and is copied by `pf init <agent-name>` into `bundles/<agent-name>/`. Layout:

- `spec.yaml` – main specification (requirements, non-functional requirements, acceptance criteria, trace).
- `spec.md` – human-readable description.
- `taint.yaml` – taint rules if used.
- `proofs/` – Lean proof directory:
  - `lean-toolchain` – Lean version.
  - `lakefile.lean` – Lake build file.
  - `Spec.lean` (and any other `.lean` files).

When adding a new bundle from the template, keep this layout so that:

- `pf bundle pack` can package the directory.
- The platform can find spec and proofs.
- The sidecar and middleware can resolve policy/automata/labeler hashes from the built bundle.

### Adding a new template (e.g. v2)

1. Copy the entire `spec-templates/v1` directory to `spec-templates/v2` (or another name).
2. Edit the copied files to define your variant (different default requirements, proof stubs, or structure).
3. To use it with the CLI:
   - If the CLI supports `--template`: run `pf init --template v2 my-agent`.
   - Otherwise, copy manually: e.g. `cp -r spec-templates/v2 bundles/my-agent` and then customize `bundles/my-agent` (e.g. rename in spec.yaml).

New templates do not require code changes in core; only the CLI `init` command would need a `--template` flag to avoid manual copy. See [Reuse and extend - Adding bundle templates](reuse-and-extend.md#adding-bundle-templates).

## Runtime components

### Minimal vs full

- **Minimal (CLI-only)**: No runtime services. You only need the CLI, `spec-templates/v1`, and `bundles/`. No Rust or Go runtime components are required.
- **Standard**: CLI + Rust workspace crates that your deployment uses (e.g. attestor, sidecar-watcher, tool-broker, labeler, wasm-sandbox, adapters/http-get, adapters/file-read). Optionally one or two Go services (e.g. admission-controller, or a single platform service) if your flow needs them.
- **Full**: All runtime and platform services: attestor, kms-proxy, tool-broker, sidecar-watcher, labeler, wasm-sandbox, admission-controller, ledger, plus Go services (api-gateway, spec-service, proof-service, build-orchestrator, evidence-service, replay-service, runtime-sidecar), console, etc.

### Rust workspace (optional crates)

The root [Cargo.toml](../../Cargo.toml) lists workspace members and documents **optional crates** in comments. These are not part of the default `cargo build --workspace` or require extra dependencies or APIs:

- **egress-firewall** – needs native Hyperscan (libhs). Build with `cargo build -p egress-firewall` when deps are available.
- **core/sdk/rust** – needs protoc. Build with `cargo build -p provability-fabric-core-sdk-rust` when deps are available.
- **sidecar-watcher/fuzz** – fuzz targets; build with `cargo build -p sidecar-watcher-fuzz` (e.g. on Linux).
- **telemetry-service, mpc-fintech, jwks-manager** – not in workspace by default; add to `members` in root `Cargo.toml` to build with the workspace.

Build them separately when their dependencies are available. See the root Cargo.toml for dependency notes (e.g. redis, Hyperscan).

### Adding a new runtime component

- **Rust**: Add a new crate under `runtime/<name>/` or `adapters/<name>/`, add it to the root `Cargo.toml` `members` array, and implement the same patterns as existing crates (config, logging, health). Document which service or sidecar invokes it and how (config, env, or discovery).
- **Go**: Add a new service under `services/<name>/` or under `runtime/` (e.g. admission-controller). Use the same Docker and health-check patterns as existing Go services if you run them in Docker. Document ports, env, and dependencies (e.g. postgres, redis).
- **Node**: Add under `runtime/ledger` or a new directory as needed; document how it is started and how it fits with the rest of the stack.

You do not need to modify core CLI or spec format to add a new runtime component; wire it via config, Docker, or orchestration and document the extension in your fork or in the developer guide.
