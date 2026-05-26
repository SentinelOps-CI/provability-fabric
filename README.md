<div align="center">

<!-- readme-banner: Provability Fabric spine (94 cols; regen: .github/assets/_build_banner.py) -->
<pre>
##############################################################################################
#                                                                                            #
#              ___                  _    _ _ _ _          ___     _        _                 #
#             | _ \_ _ _____ ____ _| |__(_) (_) |_ _  _  | __|_ _| |__ _ _(_)__              #
#             |  _/ '_/ _ \ V / _` | '_ \ | | |  _| || | | _/ _` | '_ \ '_| / _|             #
#             |_| |_| \___/\_/\__,_|_.__/_|_|_|\__|\_, | |_|\__,_|_.__/_| |_\__|             #
#                                                   |__/                                     #
#                                                                                            #
##############################################################################################
</pre>

# Provability Fabric

**Formal guarantees for agent behavior** — proofs, runtime guards, and auditable evidence in one open stack.

<sub>Prove · Enforce · Audit — formal specs, runtime policy, and evidence on one track.</sub>

<br/>

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Documentation](https://img.shields.io/badge/docs-site-brightgreen.svg)](https://provability-fabric.org)
[![Formal verification](https://img.shields.io/badge/verification-Lean-brightgreen.svg)](https://github.com/SentinelOps-CI/provability-fabric)
[![Lean CI](https://img.shields.io/badge/CI-Lean%20%28Morph%29-blue.svg)](.github/workflows/lean-morph.yml)
[![PR comments](https://img.shields.io/badge/PR%20comments-enabled-blue.svg)](#)

<br/>

<img src=".github/assets/provability-fabric - logofinal.png" alt="Provability Fabric" width="200"/>

<br/>

[Documentation](https://provability-fabric.org) · [Contributing](CONTRIBUTING.md) · [Security](SECURITY.md) · [Agent & CI guide](AGENTS.md)

</div>

---

## Why this project

Provability Fabric ties **specifications and proofs** to **what actually runs**. You get Lean-backed bundles, sidecars and admission control that enforce policy, and trails you can replay and verify as structured evidence instead of informal logging alone.

| Pillar | What it gives you |
| :--- | :--- |
| **Prove** | Specifications and Lean proofs live next to agent bundles so claims stay checkable against formal artifacts. |
| **Enforce** | Rust and Go runtimes, WASM sandboxing, and tooling brokers limit what agents can do at execution time. |
| **Audit** | Evidence formats, ledgers, and replay-oriented workflows support end-to-end accountability. |

---

## Repository map

The tree is large; use this as a compass. For CI, supply chain, and local commands, see [**AGENTS.md**](AGENTS.md).

| Area | Path | Notes |
|------|------|--------|
| **CLI & core** | [`core/`](core/) | `core/cli/pf` — Go CLI; specs, bundles, SDKs |
| **Proofs & templates** | [`spec-templates/v1`](spec-templates/v1), [`lakefile.lean`](lakefile.lean) | Lean 4; `lake build` from proof dirs |
| **Runtime** | [`runtime/`](runtime/) | Rust: attestor, KMS proxy, tool-broker, sidecar-watcher, labeler, wasm-sandbox; Node ledger; Go admission-controller |
| **Adapters** | [`adapters/`](adapters/) | HTTP/file and framework adapters (Rust, Node, Python, Go) |
| **Proof-Carrying Science** | [`docs/pcs/`](docs/pcs/README.md), [`adapters/pcs/`](adapters/pcs/) | Verify and sign science claim bundles; release admission benchmarks |
| **Platform & UI** | [`services/`](services/), [`console/`](console/), [`marketplace/`](marketplace/) | APIs, console, marketplace |
| **Config & schemas** | [`config/`](config/) | JSON schemas and specification assets |
| **Benchmarks** | [`bench/swebench/`](bench/swebench/README.md) | SWE-bench runner; Linux/WSL for real runs; details in package README |
| **Experiments** | [`experiments/`](experiments/README.md) | Eval manifests, compare/replay tooling |
| **Docs** | [`docs/`](docs/) | MkDocs site; build with `pip install -r docs/requirements.txt` then `mkdocs build` |
| **Tests** | [`tests/`](tests/) | Unit, integration, replay, privacy suites |

<details>
<summary><strong>Full top-level layout</strong> (click to expand)</summary>

```
provability-fabric/
├── core/              # CLI, SDKs, bundles
├── runtime/           # Rust / Go / Node services
├── adapters/          # Integration adapters
├── config/            # Schemas and specs
├── bench/             # Benchmarks (see bench/swebench/README.md)
├── experiments/       # Research / eval harness (see experiments/README.md)
├── tests/             # Test suites
├── docs/              # Documentation source
├── tools/             # Dev and compliance tooling
├── Cargo.toml         # Rust workspace
├── Makefile           # Compose and convenience targets
└── lean-toolchain     # Pinned Lean version
```

</details>

### Rust workspace

Toolchain: [`rust-toolchain.toml`](rust-toolchain.toml) (stable, clippy, rustfmt).

```bash
cargo build
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

**Members include:** `runtime/attestor`, `runtime/kms-proxy`, `runtime/tool-broker`, `runtime/sidecar-watcher`, `runtime/labeler`, `runtime/wasm-sandbox`, `adapters/http-get`, `adapters/file-read`. Optional or standalone crates (Hyperscan, protoc, fuzz, etc.) are documented in the root [`Cargo.toml`](Cargo.toml) and per-crate READMEs.

### How pieces fit together

- **Minimal (CLI + bundles):** [`core/cli/pf`](core/cli/pf), [`bundles/`](bundles/), [`config/`](config/). See [Reuse and extend](docs/guides/reuse-and-extend.md).
- **Full platform:** Go services, console, ledger, gateway — use Docker Compose or the launch scripts below.
- **Optional:** A CLI-only or forked minimal setup can omit `bench/`, `experiments/`, `console/`, `marketplace/`, and `demos/`.

---

## Ecosystem standards

Adopt shared schemas, replay tooling, and CI patterns alongside this repo:

- [CERT-V1](https://github.com/verifiable-ai-ci/CERT-V1) — schema and verifiers  
- [TRACE-REPLAY-KIT](https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT) — runner and oracles  
- [morph-lean-ci](https://github.com/SentinelOps-CI/morph-lean-ci) — sharded Lean CI  
- [morph-replay-runner](https://github.com/SentinelOps-CI/morph-replay-runner) — branch replays  
- [mcp-sidecar-demo](https://github.com/SentinelOps-CI/mcp-sidecar-demo) — permissions, epochs, IFC  

In-repo: [`docs/specs/standards.md`](docs/specs/standards.md), [`docs/evidence/overview.md`](docs/evidence/overview.md), [`docs/evidence/replay.md`](docs/evidence/replay.md).

### Proof-Carrying Science (PCS)

Verify lab and computation workflows with the `pf` CLI and frozen release fixtures.

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
export PCS_CORE_PATH=../pcs-core
make demo-pcs
make test-pcs-full    # full local gate; see docs/pcs/release-checklist.md
```

Full PCS documentation lives at [docs/pcs/README.md](docs/pcs/README.md).

---

## Quick start

### Option 1 — Install script (recommended)

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric
cd provability-fabric

# Linux / macOS
./scripts/install.sh
./scripts/test-new-user.sh

# Windows (Command Prompt is recommended for install scripts)
scripts\install.bat
scripts\test-new-user.bat
```

Git Bash on Windows can mis-handle paths and execution; prefer **cmd** or **PowerShell** for `install.bat` / `test-new-user.bat`. For Git Bash issues: `bash scripts/windows-troubleshoot.sh`.

### Option 2 — Web stack (Docker or scripts)

Full stack is optional; for CLI-only workflows see [Reuse and extend](docs/guides/reuse-and-extend.md).

- **Services only:** `docker compose up`  
- **Console and demos:** `docker compose --profile full up`  
- **Convenience:** `./launch-web-interfaces.sh` (Unix) or `launch-web-interfaces.bat` (Windows)

**Manual pieces (examples):**

```bash
# Ledger API (example)
cd runtime/ledger && node minimal-server.js
# → http://localhost:8080

# Console
cd console && npm install && npm start
# → http://localhost:3000

# Docs (from repo root, after pip install -r docs/requirements.txt)
mkdocs serve --dev-addr=127.0.0.1:8002
# → http://127.0.0.1:8002
```

### Option 3 — Build the CLI from source

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric
cd provability-fabric

cd core/cli/pf
go build -o pf .    # Windows: pf.exe
export PATH="$PATH:$(pwd)"          # Linux / macOS
# Windows (cmd):  set PATH=%PATH%;%CD%
# Windows (PS):   $env:PATH += ";$PWD"

cd ../../..
./pf init my-agent                  # Windows: pf.exe init my-agent

cd spec-templates/v1/proofs
lake build                          # requires Lean 4
cd ../../..

python tests/trust_fire_orchestrator.py
```

**Kubernetes:** use Helm charts under [`charts/`](charts/) and [`runtime/admission-controller/deploy/`](runtime/admission-controller/deploy/) with values suited to your cluster.

---

## Prerequisites

| Profile | You need |
|---------|-----------|
| **Minimal** | [Go 1.23+](https://go.dev/dl/) (`core/cli/pf/go.mod`). Lean optional for proofs. No Docker/Node/Rust required for bare CLI. |
| **CLI + Rust runtime** | Go + [Rust](https://rustup.rs/) (see `rust-toolchain.toml`). Docker/Node optional. |
| **Full stack** | Go, Python 3.8+, Node 18+, Rust, Docker; Lean and kubectl optional. |

**Data retention manager (if used):** PostgreSQL, S3, BigQuery, and Python deps (`psycopg2-binary`, `boto3`, `google-cloud-bigquery`, `pandas`, `pyarrow`, `pyyaml`) as required by your deployment.

---

## Architecture

High-level flow: specifications and external verifiers feed **bundles**; admission and sidecars enforce policy at runtime; the ledger and APIs expose state for operators and integrators.

```mermaid
flowchart TD
    A[Agent specification] --> B[Lean proof generation]
    B --> C[Specification bundle]
    C --> D[Admission controller]
    D --> E[Container deployment]
    E --> F[Sidecar watcher]
    F --> G[Runtime monitoring]
    G --> H[Constraint enforcement]

    I[Neural network] --> J[Marabou adapter]
    J --> K[Verification proof]
    K --> C

    L[Hybrid system] --> M[DryVR adapter]
    M --> N[Reach set]
    N --> C

    GNN[GPU neural network] --> ABC["α-β-CROWN adapter"]
    ABC --> GPUP[GPU verification proof]
    GPUP --> C

    C --> TL[Transparency ledger]
    TL --> GQL[GraphQL API]
```

**Major surfaces:** specification bundles (YAML + proofs), runtime guards (sidecars), solver adapters (e.g. Marabou, DryVR, α-β-CROWN), marketplace/console UIs, WebSocket updates, and JWT-based auth where enabled.

---

## Contributing

Contributions are welcome. Start with [CONTRIBUTING.md](CONTRIBUTING.md) and [Community governance](docs/community/governance.md).

**Typical dev loop:**

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric
cd provability-fabric

cd core/cli/pf && go build -o pf . && cd ../..
# Optional: cmd/specdoc and other Go tools as needed

# Python test deps (install where requirements.txt exists), for example:
#   pip install -r tests/integration/requirements.txt
#   pip install -r tests/proof-fuzz/requirements.txt
#   pip install -r tools/compliance/requirements.txt
#   pip install -r tools/insure/requirements.txt
#   pip install -r tools/proofbot/requirements.txt

cd console && npm install && npm start   # optional UI at http://localhost:3000
cd ..

python tests/trust_fire_orchestrator.py
```

---

## Troubleshooting

| Symptom | What to check |
|--------|----------------|
| `pf` not found | Build `core/cli/pf` and add it to `PATH` (`pf.exe` on Windows). |
| `lake build` fails | Run from the correct `proofs` directory; install [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html). |
| Python errors | Run scripts from the **repository root** unless a doc says otherwise. |
| K8s YAML / Helm | Many deployables are Helm templates, not raw `kubectl apply` files. |
| Windows paths | Prefer **forward slashes** in Git Bash; use **cmd** for `.bat` installers. |
| “Device or resource busy” | Close editors/explorers holding files; retry. |
| UI / Heroicons | Match icon names to your `package.json` / TypeScript setup (see `marketplace/ui/tsconfig.json`). |

**Windows:** Use `pf.exe` and Command Prompt for install scripts when Git Bash misbehaves. More detail: `bash scripts/windows-troubleshoot.sh`.

---

## Security

Report vulnerabilities per [SECURITY.md](SECURITY.md).

The default branch is protected by workflows including dependency review (PRs), **cargo-deny** ([`deny.toml`](deny.toml)), **actionlint**, SBOM jobs, and OpenSSF Scorecard. Enable the [dependency graph](https://docs.github.com/en/code-security/supply-chain-security/understanding-your-software-supply-chain/about-the-dependency-graph) where GitHub features require it. Overview: [AGENTS.md](AGENTS.md), [.github/WORKFLOWS.md](.github/WORKFLOWS.md), [docs/reference/ci-reference.md](docs/reference/ci-reference.md).

---

## License

Apache License 2.0 — see [LICENSE](LICENSE).

---

## Acknowledgments

- [Lean 4](https://leanprover.github.io/) — interactive theorem proving  
- [Marabou](https://github.com/NeuralNetworkVerification/Marabou) — neural network verification  
- [DryVR](https://github.com/verivital/dryvr) — hybrid systems  
- [α-β-CROWN](https://github.com/Verified-Intelligence/alpha-beta-CROWN) — GPU-accelerated NN verification  
- [Sigstore](https://sigstore.dev/) — signing and transparency  
- [Memurai](https://docs.memurai.com/) — Redis-compatible server for Windows  

---

<div align="center">

<sub>Provability Fabric — specifications, enforcement, and evidence for trustworthy agents.</sub>

</div>
