# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM golang:1.21-alpine AS builder

WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download

COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo -o main .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/

COPY --from=builder /app/main .
#COPY --from=builder /app/../../external/CERT-V1 /root/external/CERT-V1
# (CERT-V1 is bind-mounted by docker compose)
RUN mkdir -p /root/external/CERT-V1

EXPOSE 8004

CMD ["./main"]