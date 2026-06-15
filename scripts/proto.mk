# Protobuf generation and validation (included from root Makefile).
# SPDX-License-Identifier: Apache-2.0

PROTOC_INCLUDE ?= /usr/include
PROTO_API_DIR := api
PROTO_V1_DIR := api/v1
PROTO_FILES := $(wildcard $(PROTO_V1_DIR)/*.proto)
GO_PROTO_OUT := core/sdk/go/generated
TS_SDK_DIR := core/sdk/typescript
TS_PROTO_PLUGIN := $(CURDIR)/$(TS_SDK_DIR)/node_modules/.bin/protoc-gen-ts_proto
RUST_SDK_DIR := core/sdk/rust
GOLDEN_DIR := tests/fixtures/golden
API_DOCS := docs/api/api.md

.PHONY: proto-lint proto-validate proto-gen proto-gen-go proto-gen-ts proto-gen-rust \
	proto-fixtures proto-compat-test proto-docs

proto-lint:
	@$(ECHOOK) "Linting protobuf files..."
	@command -v protoc >/dev/null 2>&1 || { echo "protoc is required"; exit 1; }
	@for f in $(PROTO_FILES); do \
		echo "  $$f"; \
		protoc --proto_path=$(PROTO_API_DIR) $(if $(wildcard $(PROTOC_INCLUDE)),--proto_path=$(PROTOC_INCLUDE),) \
			--descriptor_set_out=/dev/null "$$f" || exit 1; \
	done
	@$(ECHOOK) "Protobuf lint passed"

proto-validate: proto-lint

proto-gen-go:
	@$(ECHOOK) "Generating Go protobuf bindings..."
	@mkdir -p $(GO_PROTO_OUT)
	@protoc --proto_path=$(PROTO_API_DIR) $(if $(wildcard $(PROTOC_INCLUDE)),--proto_path=$(PROTOC_INCLUDE),) \
		--go_out=$(GO_PROTO_OUT) --go_opt=paths=source_relative \
		--go-grpc_out=$(GO_PROTO_OUT) --go-grpc_opt=paths=source_relative \
		$(PROTO_FILES)

proto-gen-ts:
	@$(ECHOOK) "Generating TypeScript protobuf bindings..."
	@test -x "$(TS_PROTO_PLUGIN)" || { echo "Install ts-proto in $(TS_SDK_DIR) (npm install ts-proto)"; exit 1; }
	@mkdir -p $(TS_SDK_DIR)/generated
	@protoc --proto_path=$(PROTO_API_DIR) $(if $(wildcard $(PROTOC_INCLUDE)),--proto_path=$(PROTOC_INCLUDE),) \
		--plugin=protoc-gen-ts_proto=$(TS_PROTO_PLUGIN) \
		--ts_proto_out=$(TS_SDK_DIR)/generated \
		--ts_proto_opt=esModuleInterop=true \
		--ts_proto_opt=forceLong=string \
		--ts_proto_opt=useOptionals=messages \
		$(PROTO_FILES)

proto-gen-rust:
	@$(ECHOOK) "Generating Rust protobuf bindings (via protoc-gen-tonic)..."
	@command -v protoc-gen-tonic >/dev/null 2>&1 || { echo "protoc-gen-tonic is required (cargo install protoc-gen-tonic)"; exit 1; }
	@mkdir -p $(RUST_SDK_DIR)/.proto-gen-out/provability_fabric/api/v1
	@protoc --proto_path=$(PROTO_API_DIR) $(if $(wildcard $(PROTOC_INCLUDE)),--proto_path=$(PROTOC_INCLUDE),) \
		--plugin=protoc-gen-tonic=$$(command -v protoc-gen-tonic) \
		--tonic_out=$(RUST_SDK_DIR)/.proto-gen-out \
		$(PROTO_FILES)

proto-gen: proto-gen-go proto-gen-ts proto-gen-rust
	@$(ECHOOK) "Protobuf code generation complete"

proto-fixtures:
	@$(ECHOOK) "Refreshing protobuf golden fixtures..."
	@mkdir -p $(GOLDEN_DIR)
	@python -c "import json, pathlib; \
p = pathlib.Path('$(GOLDEN_DIR)/proto_manifest.json'); \
p.write_text(json.dumps(sorted([pathlib.Path(f).name for f in '$(PROTO_FILES)'.split()]), indent=2) + '\n')"
	@$(ECHOOK) "Golden fixtures updated under $(GOLDEN_DIR)"

proto-compat-test:
	@$(ECHOOK) "Checking protobuf backward compatibility..."
	@python scripts/proto_compat_check.py

proto-docs:
	@$(ECHOOK) "Generating protobuf API documentation..."
	@mkdir -p docs/api
	@python scripts/proto_docs.py
