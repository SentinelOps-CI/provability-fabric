set shell := ["bash", "-cu"]

root := justfile_directory()
pcs_core := env_var_or_default('PCS_CORE_PATH', root / '../pcs-core')

default:
    @just test-pcs

test-pcs:
    make test-pcs

test-pcs-full:
    make test-pcs-full

test-pcs-benchmark:
    bash "{{root}}/scripts/pcs-benchmark-admission.sh" || powershell -NoProfile -ExecutionPolicy Bypass -File "{{root}}/scripts/pcs-benchmark-admission.ps1"

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
