# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Multi-stage build for optimal image size and security
FROM rust:1.75-alpine AS builder

# Install build dependencies
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig \
    && rm -rf /var/cache/apk/*

# Set working directory
WORKDIR /app

# Copy dependency files
COPY Cargo.toml Cargo.lock ./

# Create a dummy main.rs to build dependencies
RUN mkdir src && echo "fn main() {}" > src/main.rs

# Build dependencies (this layer will be cached)
RUN cargo build --release --target x86_64-unknown-linux-musl

# Copy source code
COPY src/ ./src/

# Build the application
RUN cargo build --release --target x86_64-unknown-linux-musl

# Runtime stage
FROM alpine:3.19

# Install runtime dependencies
RUN apk add --no-cache \
    ca-certificates \
    libc6-compat \
    && rm -rf /var/cache/apk/*

# Create non-root user
RUN addgroup -g 1001 -S appgroup && \
    adduser -u 1001 -S appuser -G appgroup

# Set working directory
WORKDIR /app

# Copy binary from builder stage
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/sidecar-watcher ./

# Copy policy files
COPY policy/ ./policy/

# Set ownership
RUN chown -R appuser:appgroup /app

# Switch to non-root user
USER appuser

# Expose port (if needed)
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

# Run the application
CMD ["./sidecar-watcher"]

# Labels for better image management
LABEL org.opencontainers.image.title="Provability-Fabric Sidecar Watcher"
LABEL org.opencontainers.image.description="Policy enforcement sidecar for Kubernetes workloads"
LABEL org.opencontainers.image.vendor="Provability-Fabric"
LABEL org.opencontainers.image.source="https://github.com/provability-fabric/provability-fabric"
LABEL org.opencontainers.image.licenses="Apache-2.0"
