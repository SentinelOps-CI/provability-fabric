# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Build from repository root: docker build -f runtime/retrieval-gateway/Dockerfile .

FROM rust:1.88-bookworm AS builder
WORKDIR /app
COPY core/crypto/dsse-rs ./core/crypto/dsse-rs
COPY runtime/retrieval-gateway ./runtime/retrieval-gateway
# Minimal workspace: root Cargo.toml lists members not copied into this context.
RUN cat > Cargo.toml <<'EOF'
[workspace]
members = [
    "core/crypto/dsse-rs",
    "runtime/retrieval-gateway",
]
resolver = "2"
EOF
RUN cargo build --release -p retrieval-gateway

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates wget \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/retrieval-gateway /usr/local/bin/
EXPOSE 8080
ENV PORT=8080
CMD ["retrieval-gateway"]
