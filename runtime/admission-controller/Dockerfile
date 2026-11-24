# syntax=docker/dockerfile:1.7
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

FROM golang:1.25-alpine AS builder
ENV GOTOOLCHAIN=local

WORKDIR /app
COPY go.mod go.sum ./
RUN --mount=type=cache,target=/go/pkg/mod go mod download

COPY . .
RUN --mount=type=cache,target=/root/.cache/go-build \
    CGO_ENABLED=0 GOOS=linux go build -mod=readonly -trimpath -buildvcs=false -ldflags="-s -w" -o admission-controller .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/

COPY --from=builder /app/admission-controller .
COPY --from=builder /app/certs /etc/certs

EXPOSE 8443

CMD ["./admission-controller"] 