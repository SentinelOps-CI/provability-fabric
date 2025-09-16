# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps

# ---------- builder stage ----------
FROM rust:1.82-bookworm AS builder

WORKDIR /app

# Cache deps: copy manifests first
COPY Cargo.toml Cargo.lock ./

# Create a dummy src to resolve deps and prime cache
RUN mkdir -p src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# Now copy real sources and build
COPY src ./src
RUN cargo build --release --locked

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
