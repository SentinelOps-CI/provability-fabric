# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

FROM golang:1.21-alpine AS builder

WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download

COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo -o main .

FROM alpine:latest
RUN apk --no-cache add ca-certificates python3 py3-pip
WORKDIR /root/

COPY --from=builder /app/main .
# COPY --from=builder /app/../../external/TRACE-REPLAY-KIT /root/external/TRACE-REPLAY-KIT
# (kit is bind-mounted by docker compose)
RUN mkdir -p /app/external/TRACE-REPLAY-KIT

EXPOSE 8005

CMD ["./main"]