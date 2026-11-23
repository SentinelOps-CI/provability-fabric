# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Multi-stage build for optimal image size and security
# Build from the repository root using its canonical dependency graph.
# docker build --file runtime/attestor/Dockerfile .
FROM rust:1.99.1-alpine AS builder

RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig

WORKDIR /app
COPY . .
RUN cargo +1.99.1 build --locked --release -p attestor

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
COPY --from=builder /app/target/release/attestor ./

# Set ownership
RUN chown -R appuser:appgroup /app

# Switch to non-root user
USER appuser

# Expose port (if needed)
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD wget -q -O /dev/null http://127.0.0.1:8080/health || exit 1

# Run the application
CMD ["./attestor"]

# Labels for better image management
LABEL org.opencontainers.image.title="Provability-Fabric Attestor"
LABEL org.opencontainers.image.description="Cryptographic attestation service for workload verification"
LABEL org.opencontainers.image.vendor="Provability-Fabric"
LABEL org.opencontainers.image.source="https://github.com/provability-fabric/provability-fabric"
LABEL org.opencontainers.image.licenses="Apache-2.0"
