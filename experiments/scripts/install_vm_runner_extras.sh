#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Optional packages for GCP/Debian VMs: tmux/screen so long SWE-bench gates survive SSH disconnect.
# Run once: bash experiments/scripts/install_vm_runner_extras.sh
set -euo pipefail

if ! command -v apt-get >/dev/null 2>&1; then
  echo "apt-get not found; install tmux and screen with your OS package manager." >&2
  exit 1
fi

sudo apt-get update
sudo apt-get install -y tmux screen
echo "Installed tmux and screen. Example: tmux new -s abgate"
