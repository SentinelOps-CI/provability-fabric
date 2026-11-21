# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps

# Build from the repository root with its canonical workspace and Cargo.lock.
# docker build -f runtime/telemetry-service/Dockerfile .
FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
COPY . .
RUN cargo +1.99.1 build --locked --release -p telemetry-service

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
