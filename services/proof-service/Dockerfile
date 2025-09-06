# syntax=docker/dockerfile:1.7
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM golang:1.21-alpine AS builder

WORKDIR /app
COPY go.mod go.sum ./
RUN --mount=type=cache,target=/go/pkg/mod go mod download

COPY . .
RUN --mount=type=cache,target=/root/.cache/go-build \
    CGO_ENABLED=0 GOOS=linux go build -trimpath -buildvcs=false -ldflags="-s -w" -o main .

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates curl python3 python3-pip git && rm -rf /var/lib/apt/lists/*
WORKDIR /root/

# Install Lean 4 (using Debian-compatible approach)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Verify lake (Lean build tool) is available
RUN /root/.elan/bin/lake --help || true

COPY --from=builder /app/main .

EXPOSE 8002

CMD ["./main"]