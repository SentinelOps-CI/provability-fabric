# PCS adapter — local targets and delegation to repo-root Make/just.
# Run `make test-pcs-benchmark` from here or from the repository root.

ROOT := $(abspath ../..)

.PHONY: test test-pcs-benchmark validate-pcs-benchmark-bundle test-pcs-full help

help:
	@echo "From adapters/pcs (delegates bench targets to repo root):"
	@echo "  make test                      — go test ./..."
	@echo "  make test-pcs-benchmark        — full admission benchmark gate"
	@echo "  make validate-pcs-benchmark-bundle — validate labtrust bundle"
	@echo "  make test-pcs-full             — unit + RC + fixtures + benchmarks"
	@echo ""
	@echo "Or from repo root: make test-pcs-benchmark"

test:
	go test ./... -count=1

test-pcs-benchmark:
	$(MAKE) -C $(ROOT) test-pcs-benchmark

validate-pcs-benchmark-bundle:
	$(MAKE) -C $(ROOT) validate-pcs-benchmark-bundle

test-pcs-full:
	$(MAKE) -C $(ROOT) test-pcs-full
