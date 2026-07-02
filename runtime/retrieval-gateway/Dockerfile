# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Build from repository root: docker build -f runtime/retrieval-gateway/Dockerfile .

FROM rust:1.88-bookworm AS builder
WORKDIR /app

COPY Cargo.toml Cargo.lock ./
COPY runtime/retrieval-gateway/Cargo.toml runtime/retrieval-gateway/
COPY core/crypto/dsse-rs/Cargo.toml core/crypto/dsse-rs/
COPY core/crypto/dsse-rs/src core/crypto/dsse-rs/src
COPY runtime/retrieval-gateway/src runtime/retrieval-gateway/src
RUN cargo build --release -p retrieval-gateway

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates wget \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/retrieval-gateway /usr/local/bin/
EXPOSE 8080
ENV PORT=8080
CMD ["retrieval-gateway"]
