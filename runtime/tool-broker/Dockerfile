# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Build from repository root: docker build -f runtime/tool-broker/Dockerfile .

FROM rust:1.99.1-bookworm AS builder
WORKDIR /app
# Use the reviewed repository Cargo.lock. A temporary two-crate workspace
# resolves newer transitive packages independently of the production graph.
COPY . .
# Override the root rust-toolchain selector with the image's pinned compiler.
RUN cargo +1.99.1 build --locked --release -p tool-broker

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/tool-broker /usr/local/bin/tool-broker
ENV KERNEL_URL=http://runtime-sidecar:8006
CMD ["tool-broker"]
