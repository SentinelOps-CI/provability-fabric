# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM golang:1.21-alpine AS builder

WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download

COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo -o main .

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates curl python3 python3-pip git && rm -rf /var/lib/apt/lists/*
WORKDIR /root/

# Install Lean 4 (using Debian-compatible approach)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Install lake (Lean build tool)
RUN /root/.elan/bin/lake --help || true

COPY --from=builder /app/main .

EXPOSE 8002

CMD ["./main"]