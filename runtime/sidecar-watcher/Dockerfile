# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps

# ---------- builder stage ----------
FROM rust:1.85-bookworm AS builder

WORKDIR /app

# Cache deps: copy manifests first
COPY Cargo.toml ./
# If you have a workspace, also copy Cargo.toml files of members:
# COPY crates/*/Cargo.toml crates/*/

# Create a dummy src to resolve deps and prime cache
RUN mkdir -p src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# Now copy real sources and build
COPY src ./src
# If workspace: COPY crates ./crates
RUN cargo build --release

# ---------- runtime stage ----------
FROM debian:bookworm-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user for security
RUN groupadd -r sidecar && useradd -r -g sidecar -d /home/sidecar -s /sbin/nologin sidecar

# Create necessary directories with proper permissions
RUN mkdir -p /home/sidecar /tmp /var/log && \
    chown -R sidecar:sidecar /home/sidecar /tmp /var/log && \
    chmod 755 /home/sidecar /tmp /var/log

WORKDIR /home/sidecar

# Copy binary and set ownership
COPY --from=builder /app/target/release/sidecar-watcher /usr/local/bin/sidecar-watcher
RUN chown sidecar:sidecar /usr/local/bin/sidecar-watcher && \
    chmod +x /usr/local/bin/sidecar-watcher

# Switch to non-root user
USER sidecar

EXPOSE 8006 9090
CMD ["sidecar-watcher"]
