set shell := ["bash", "-cu"]

root := justfile_directory()
pcs_core := env_var_or_default('PCS_CORE_PATH', root / '../pcs-core')

default:
    @just test-pcs

# ---------- Local launch (thin wrappers over Make / compose contracts) ----------
# See docs/dev/local-workflows.md for the canonical task → command → ports matrix.

up target="platform":
    #!/usr/bin/env bash
    set -euo pipefail
    case "{{target}}" in
      platform|plat)
        make platform-up
        ;;
      ledger)
        make ledger-up
        ;;
      full)
        make full-up
        ;;
      enforcement|enforce)
        make enforcement-up
        ;;
      sidecar)
        echo "Local sidecar (compose-aligned port 8006):"
        echo "  cd runtime/sidecar-watcher && PORT=8006 LEDGER_URL=http://localhost:4000 cargo run"
        echo "Or: make platform-up  # includes runtime-sidecar"
        ;;
      broker|tool-broker)
        echo "Local tool-broker (KERNEL_URL → sidecar :8006):"
        echo "  cd runtime/tool-broker && KERNEL_URL=http://localhost:8006 cargo run"
        echo "Or: make full-up  # starts tool-broker under profile full"
        ;;
      *)
        echo "Usage: just up platform|ledger|sidecar|broker|enforcement|full" >&2
        exit 1
        ;;
    esac

platform-up:
    make platform-up

ledger-up:
    make ledger-up

full-up:
    make full-up

compose-smoke:
    make compose-smoke

check-wiring:
    make check-wiring

test-pcs:
    make test-pcs

test-pcs-full:
    make test-pcs-full

pcs-release-gate:
    make pcs-release-gate

test-pcs-benchmark:
    bash "{{root}}/scripts/pcs-benchmark-admission.sh" || powershell -NoProfile -ExecutionPolicy Bypass -File "{{root}}/scripts/pcs-benchmark-admission.ps1"

validate-pcs-benchmark-bundle:
    bash "{{root}}/scripts/pcs-validate-benchmark-bundle.sh" "{{root}}/benchmark_runs/labtrust_admission"

pcs-bench-producer:
    make pcs-bench-producer

export-pcs-benchmark-ingest-reference:
    make export-pcs-benchmark-ingest-reference

pcs-bench-validate-ingest ingest="{{root}}/benchmark_runs/labtrust_admission/pcs_bench_ingest.v0.json" bundle_dir="{{root}}/benchmark_runs/labtrust_admission":
    bash "{{root}}/scripts/pcs-bench-validate-ingest.sh" \
      --input "{{ingest}}" \
      --bundle-dir "{{bundle_dir}}" \
      --pcs-core "{{pcs_core}}" \
      --release-grade

pcs-schema-diff:
    bash "{{root}}/scripts/pcs-schema-diff.sh" "{{pcs_core}}"

pcs-schema-sync:
    bash "{{root}}/scripts/pcs-schema-sync.sh" "{{pcs_core}}"

freeze-pcs-labtrust-signed:
    make freeze-pcs-labtrust-signed

freeze-pcs-labtrust-release:
    make freeze-pcs-labtrust-release

pcs-v01-pf-chain:
    # bash when go is on PATH (CI/Linux); PowerShell fallback on Windows Git Bash without go
    PF_RELEASE_MODE=1 bash "{{root}}/scripts/pcs-pf-clean-chain.sh" "{{root}}/tests/pcs/fixtures/labtrust-release" || powershell -NoProfile -ExecutionPolicy Bypass -File "{{root}}/scripts/pcs-pf-clean-chain.ps1" "{{root}}/tests/pcs/fixtures/labtrust-release"

pcs-v01-clean-chain:
    bash "{{root}}/scripts/run-pcs-v01-clean-chain.sh"

pcs-v01-clean-chain-ps1:
    powershell -NoProfile -ExecutionPolicy Bypass -File "{{root}}/scripts/run-pcs-v01-clean-chain.ps1"

pcs-validate file:
    bash "{{root}}/scripts/pcs" validate "{{file}}"

scientific_memory := env_var_or_default('SCIENTIFIC_MEMORY_ROOT', root / '../scientific-memory')

pcs-import-bundle bundle:
    cd "{{scientific_memory}}" && just pcs-import-bundle "{{bundle}}"

pcs-render-claim claim_id:
    cd "{{scientific_memory}}" && just pcs-render-claim "{{claim_id}}"

demo-pcs:
    make demo-pcs

demo-pcs-release:
    make demo-pcs-release

validate-pcs-fixtures:
    make validate-pcs-fixtures
