# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps

# Build from the repository root with its canonical workspace and Cargo.lock.
# docker build -f runtime/jwks-manager/Dockerfile .
FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
COPY . .
RUN cargo +1.99.1 build --locked --release -p jwks-manager

# ---------- runtime stage ----------
FROM debian:bookworm-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user for security
RUN groupadd -r jwks && useradd -r -g jwks -d /home/jwks -s /sbin/nologin jwks

# Create necessary directories with proper permissions
RUN mkdir -p /home/jwks && \
    chown -R jwks:jwks /home/jwks && \
    chmod 755 /home/jwks

WORKDIR /home/jwks

# Copy binary and set ownership
COPY --from=builder /app/target/release/jwks-manager /usr/local/bin/jwks-manager
RUN chown jwks:jwks /usr/local/bin/jwks-manager && \
    chmod +x /usr/local/bin/jwks-manager

# Switch to non-root user
USER jwks

EXPOSE 8083
CMD ["jwks-manager"]
