# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Multi-stage build for optimal image size and security
FROM rust:1.99.1-alpine AS builder

# Install build dependencies (no openssl: reqwest uses rustls-tls)
RUN apk add --no-cache \
    musl-dev \
    pkgconfig \
    && rm -rf /var/cache/apk/*

# Build with the canonical workspace and reviewed root Cargo.lock.
# Override any floating Rust toolchain selector from the copied source.
WORKDIR /app
COPY . .
RUN cargo +1.99.1 build --locked --release -p egress-firewall \
    --no-default-features --features mimalloc

# Runtime stage
FROM alpine:3.19

# Install runtime dependencies (wget for compose/Dockerfile healthchecks)
RUN apk add --no-cache \
    ca-certificates \
    libc6-compat \
    wget \
    && rm -rf /var/cache/apk/*

# Create non-root user
RUN addgroup -g 1001 -S appgroup && \
    adduser -u 1001 -S appuser -G appgroup

# Set working directory
WORKDIR /app

# Copy binary from builder stage
COPY --from=builder /app/target/release/egress-firewall ./

# Copy policy files
COPY runtime/egress-firewall/policies/ ./policies/

# Set ownership
RUN chown -R appuser:appgroup /app

# Switch to non-root user
USER appuser

# Expose port (matches compose mapping and actix bind)
EXPOSE 8081

# Health check uses GET (not wget --spider/HEAD) so /health must respond to GET.
HEALTHCHECK --interval=10s --timeout=5s --start-period=20s --retries=12 \
    CMD wget -q -O /dev/null http://127.0.0.1:8081/health || exit 1

# Run the application
CMD ["./egress-firewall"]

# Labels for better image management
LABEL org.opencontainers.image.title="Provability-Fabric Egress Firewall"
LABEL org.opencontainers.image.description="AI-powered egress traffic filtering and PII detection"
LABEL org.opencontainers.image.vendor="Provability-Fabric"
LABEL org.opencontainers.image.source="https://github.com/provability-fabric/provability-fabric"
LABEL org.opencontainers.image.licenses="Apache-2.0"
