# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

FROM rust:1.88-bookworm AS builder
WORKDIR /app
COPY Cargo.toml ./
COPY src ./src
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates wget \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/retrieval-gateway /usr/local/bin/
EXPOSE 8080
ENV PORT=8080
CMD ["retrieval-gateway"]
