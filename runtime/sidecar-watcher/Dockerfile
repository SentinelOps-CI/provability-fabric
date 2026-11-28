# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps
#
# Build from repository root: docker build -f runtime/sidecar-watcher/Dockerfile .

FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
# Build against the canonical workspace and reviewed Cargo.lock.
# The root .dockerignore excludes local build outputs and environment files.
COPY . .
# Override any floating Rust toolchain selector in the copied source.
RUN cargo +1.99.1 build --locked --release -p sidecar-watcher
# Collect the locked all-target certificate data license, even when the
# Linux build does not download the platform-specific crate.
RUN cargo +1.99.1 fetch --locked
RUN set -eu; \
    mkdir -p /app/third-party-licenses; \
    set -- "${CARGO_HOME:-/usr/local/cargo}"/registry/src/*/webpki-root-certs-1.0.12/LICENSE; \
    test "$#" -eq 1; \
    test -s "$1"; \
    cp "$1" /app/third-party-licenses/webpki-root-certs-1.0.12.LICENSE

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
COPY --from=builder /app/third-party-licenses/ /usr/share/doc/sidecar-watcher/third-party-licenses/
RUN chown sidecar:sidecar /usr/local/bin/sidecar-watcher && \
    chmod +x /usr/local/bin/sidecar-watcher

USER sidecar

EXPOSE 8006 9090
CMD ["sidecar-watcher"]
