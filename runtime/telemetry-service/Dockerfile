# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps

# ---------- builder stage ----------
FROM rust:1.86-bookworm AS builder

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
RUN groupadd -r telemetry && useradd -r -g telemetry -d /home/telemetry -s /sbin/nologin telemetry

# Create necessary directories with proper permissions
RUN mkdir -p /home/telemetry && \
    chown -R telemetry:telemetry /home/telemetry && \
    chmod 755 /home/telemetry

WORKDIR /home/telemetry

# Copy binary and set ownership
COPY --from=builder /app/target/release/telemetry-service /usr/local/bin/telemetry-service
RUN chown telemetry:telemetry /usr/local/bin/telemetry-service && \
    chmod +x /usr/local/bin/telemetry-service

# Switch to non-root user
USER telemetry

EXPOSE 8084
CMD ["telemetry-service"]
