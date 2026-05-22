#!/usr/bin/env bash
set -euo pipefail
export PATH=/usr/local/go/bin:$PATH
apt-get update -qq && apt-get install -qq -y git >/dev/null 2>&1
git clone --depth 1 https://github.com/SentinelOps-CI/provability-fabric.git /pf
cd /pf
git clone --depth 1 --filter=blob:none --sparse https://github.com/SentinelOps-CI/pcs-core.git pcs-core
cd pcs-core
git sparse-checkout set schemas python examples/labtrust-release
cd /pf/adapters/pcs
export PCS_CORE_PATH=/pf/pcs-core
export GITHUB_ACTIONS=true
go test ./... -count=1
