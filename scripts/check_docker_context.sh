#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Probe the actual Docker build context, not an approximation of ignore rules.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v docker >/dev/null 2>&1 || { echo 'docker is required for context verification' >&2; exit 2; }

tmp="$(mktemp -d)"
image_id=""
container_id=""
cleanup() {
  if [[ -n "${container_id}" ]]; then
    docker rm -f "${container_id}" >/dev/null 2>&1 || true
  fi
  if [[ -n "${image_id}" ]]; then
    docker image rm "${image_id}" >/dev/null 2>&1 || true
  fi
  rm -rf -- "${tmp}"
}
trap cleanup EXIT

context="${tmp}/context"
output="${tmp}/extracted"
mkdir -p "${context}/runtime/sidecar-watcher/src" \
  "${context}/runtime/retrieval-gateway" \
  "${context}/private" "${context}/runs" \
  "${context}/benchmark_runs" "${context}/release-run" \
  "${context}/.aws" "${context}/.ssh" "${context}/.kube" \
  "${context}/.local/secrets"
cp "${ROOT}/.dockerignore" "${context}/.dockerignore"

for path in Cargo.toml Cargo.lock runtime/sidecar-watcher/src/lib.rs runtime/retrieval-gateway/Cargo.toml; do
  printf 'safe-test-artifact\n' > "${context}/${path}"
done
sensitive=(
  .env .env.production .env.production.local .env.example
  .npmrc .pypirc .netrc
  runtime/sidecar-watcher/.env.staging
  .aws/credentials .ssh/id_rsa .kube/config
  .local/secrets/retrieval-receipt-signing-key.pem
  private/secret.json runs/private.json benchmark_runs/private.json
  release-run/private.json
)
for path in "${sensitive[@]}"; do
  printf 'do-not-copy\n' > "${context}/${path}"
done

# A scratch image copies the context without pulling any external image.
# docker create + docker cp inspect the real context as interpreted by Moby.
image_id="$(docker build --quiet --no-cache -f - "${context}" <<'DOCKERFILE'
FROM scratch
COPY . /payload
CMD ["/nonexistent"]
DOCKERFILE
)"
container_id="$(docker create "${image_id}")"
mkdir -p "${output}"
docker cp "${container_id}:/payload/." "${output}/"

for path in Cargo.toml Cargo.lock runtime/sidecar-watcher/src/lib.rs runtime/retrieval-gateway/Cargo.toml; do
  if [[ ! -s "${output}/${path}" ]]; then
    echo "missing required build-context source: ${path}" >&2
    exit 1
  fi
done
for path in "${sensitive[@]}"; do
  if [[ -e "${output}/${path}" ]]; then
    echo "sensitive local file transmitted to Docker build context: ${path}" >&2
    exit 1
  fi
done
printf '%s\n' 'Docker context includes required source and excludes all sensitive fixtures'
