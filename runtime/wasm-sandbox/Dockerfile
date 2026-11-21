# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Build from repository root: docker build -f runtime/wasm-sandbox/Dockerfile .

FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
# Use the reviewed canonical workspace graph and Cargo.lock.
COPY . .
RUN cargo +1.99.1 build --locked --release -p wasm-sandbox

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd --system wasm \
    && useradd --system --gid wasm --home-dir /nonexistent --shell /usr/sbin/nologin wasm
COPY --from=builder /app/target/release/wasm-sandbox /usr/local/bin/wasm-sandbox
USER wasm
ENTRYPOINT ["wasm-sandbox"]
