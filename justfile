set shell := ["bash", "-cu"]

root := justfile_directory()
pcs_core := env_var_or_default('PCS_CORE_PATH', root / '../pcs-core')

default:
    @just test-pcs

test-pcs:
    make test-pcs

pcs-schema-diff:
    bash "{{root}}/scripts/pcs-schema-diff.sh" "{{pcs_core}}"

pcs-schema-sync:
    bash "{{root}}/scripts/pcs-schema-sync.sh" "{{pcs_core}}"

demo-pcs:
    make demo-pcs
