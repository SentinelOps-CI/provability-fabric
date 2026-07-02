# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Build from repository root: docker build -f runtime/wasm-sandbox/Dockerfile .

FROM rust:1.88-bookworm AS builder
WORKDIR /app
COPY runtime/wasm-sandbox ./runtime/wasm-sandbox
RUN cat > Cargo.toml <<'EOF'
[workspace]
members = ["runtime/wasm-sandbox"]
resolver = "2"
EOF
RUN cargo build --release -p wasm-sandbox

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/wasm-sandbox /usr/local/bin/wasm-sandbox
ENTRYPOINT ["wasm-sandbox"]
