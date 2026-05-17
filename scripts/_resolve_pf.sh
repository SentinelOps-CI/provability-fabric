# shellcheck shell=bash
# Resolve pf CLI for bash scripts (Git Bash / WSL). Source and call resolve_pf ROOT.
# Sets PF_CMD as a bash array: "${PF_CMD[@]}" verify science-claim ...

resolve_go_bin() {
  if command -v go >/dev/null 2>&1; then
    command -v go
    return 0
  fi
  local candidates=()
  if [[ -n "${ProgramFiles:-}" ]]; then
    candidates+=("${ProgramFiles}/Go/bin/go.exe")
  fi
  if [[ -n "${ProgramFiles(x86):-}" ]]; then
    candidates+=("${ProgramFiles(x86)}/Go/bin/go.exe")
  fi
  candidates+=(
    "/mnt/c/Program Files/Go/bin/go.exe"
    "/c/Program Files/Go/bin/go.exe"
    "/c/Program Files (x86)/Go/bin/go.exe"
  )
  local c
  for c in "${candidates[@]}"; do
    if [[ -n "${c}" && -x "${c}" ]]; then
      echo "${c}"
      return 0
    fi
  done
  return 1
}

resolve_pf() {
  local root="$1"
  PF_CMD=()
  if [[ -n "${PF:-}" ]]; then
    # shellcheck disable=SC2206
    PF_CMD=(${PF})
    return 0
  fi
  local pf_exe="${root}/core/cli/pf/pf.exe"
  if [[ -x "${pf_exe}" ]]; then
    PF_CMD=("${pf_exe}")
    return 0
  fi
  local go_bin
  if ! go_bin="$(resolve_go_bin)"; then
    echo "go not found; install Go or build core/cli/pf/pf.exe (set PF=...)" >&2
    return 1
  fi
  if [[ ! -x "${pf_exe}" ]]; then
    (cd "${root}/core/cli/pf" && "${go_bin}" build -o pf.exe .) || return 1
  fi
  if [[ -x "${pf_exe}" ]]; then
    PF_CMD=("${pf_exe}")
    return 0
  fi
  PF_CMD=("${go_bin}" -C "${root}/core/cli/pf" run .)
  return 0
}

run_pf() {
  if [[ ${#PF_CMD[@]} -eq 0 ]]; then
    echo "run_pf: call resolve_pf first" >&2
    return 1
  fi
  "${PF_CMD[@]}" "$@"
}

# rebuild_pf compiles core/cli/pf/pf.exe (use before fixture freeze so adapter changes apply).
rebuild_pf() {
  local root="$1"
  local go_bin
  if ! go_bin="$(resolve_go_bin)"; then
    echo "go not found; cannot rebuild pf" >&2
    return 1
  fi
  (cd "${root}/core/cli/pf" && "${go_bin}" build -o pf.exe .) || return 1
  PF_CMD=("${root}/core/cli/pf/pf.exe")
  return 0
}
