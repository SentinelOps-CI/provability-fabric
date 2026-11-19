# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Build from repository root: docker build -f runtime/retrieval-gateway/Dockerfile .

FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
# Build from the canonical workspace and reviewed Cargo.lock.
# The root .dockerignore excludes local build outputs and environment files.
COPY . .
# Override any floating Rust toolchain selector in the copied source.
RUN cargo +1.99.1 build --locked --release -p retrieval-gateway

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates wget \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /app
COPY runtime/retrieval-gateway/abac.yaml ./abac.yaml
COPY --from=builder /app/target/release/retrieval-gateway /usr/local/bin/
EXPOSE 8080
ENV PORT=8080
CMD ["retrieval-gateway"]
