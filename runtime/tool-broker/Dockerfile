# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Build from repository root: docker build -f runtime/tool-broker/Dockerfile .

FROM rust:1.88-bookworm AS builder
WORKDIR /app
COPY core/crypto/dsse-rs ./core/crypto/dsse-rs
COPY runtime/tool-broker ./runtime/tool-broker
# Minimal workspace: root Cargo.toml lists members not copied into this context.
RUN cat > Cargo.toml <<'EOF'
[workspace]
members = [
    "core/crypto/dsse-rs",
    "runtime/tool-broker",
]
resolver = "2"
EOF
RUN cargo build --release -p tool-broker

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/tool-broker /usr/local/bin/tool-broker
ENV KERNEL_URL=http://runtime-sidecar:8006
CMD ["tool-broker"]
