# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

FROM golang:1.23-alpine AS builder

WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download

COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo -o admission-controller .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/

COPY --from=builder /app/admission-controller .
COPY --from=builder /app/certs /etc/certs

EXPOSE 8443

CMD ["./admission-controller"] 