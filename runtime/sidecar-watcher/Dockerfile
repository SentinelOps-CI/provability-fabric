# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps
#
# Build from repository root: docker build -f runtime/sidecar-watcher/Dockerfile .

FROM rust:1.88-bookworm AS builder
WORKDIR /app
COPY core/crypto/dsse-rs ./core/crypto/dsse-rs
COPY runtime/sidecar-watcher ./runtime/sidecar-watcher
# Minimal workspace: root Cargo.toml lists members not copied into this context.
RUN cat > Cargo.toml <<'EOF'
[workspace]
members = [
    "core/crypto/dsse-rs",
    "runtime/sidecar-watcher",
]
resolver = "2"
EOF
RUN cargo build --release -p sidecar-watcher

FROM debian:bookworm-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

RUN groupadd -r sidecar && useradd -r -g sidecar -d /home/sidecar -s /sbin/nologin sidecar

RUN mkdir -p /home/sidecar /tmp /var/log && \
    chown -R sidecar:sidecar /home/sidecar /tmp /var/log && \
    chmod 755 /home/sidecar /tmp /var/log

WORKDIR /home/sidecar

COPY --from=builder /app/target/release/sidecar-watcher /usr/local/bin/sidecar-watcher
RUN chown sidecar:sidecar /usr/local/bin/sidecar-watcher && \
    chmod +x /usr/local/bin/sidecar-watcher

USER sidecar

EXPOSE 8006 9090
CMD ["sidecar-watcher"]
