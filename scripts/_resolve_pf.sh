# shellcheck shell=bash
# Resolve pf CLI for bash scripts (Git Bash / WSL). Source and call resolve_pf ROOT.
# Sets PF_CMD as a bash array: "${PF_CMD[@]}" verify science-claim ...

path_exists() {
  local p="$1"
  [[ -n "${p}" ]] || return 1
  if [[ "${p}" == *.exe ]]; then
    [[ -f "${p}" ]]
  else
    [[ -x "${p}" ]]
  fi
}

resolve_go_bin() {
  if command -v go >/dev/null 2>&1; then
    command -v go
    return 0
  fi
  local candidates=()
  if [[ -n "${ProgramFiles:-}" ]]; then
    candidates+=("${ProgramFiles}/Go/bin/go.exe")
  fi
  local pf86
  pf86="$(printenv 'ProgramFiles(x86)' 2>/dev/null || true)"
  if [[ -n "${pf86}" ]]; then
    candidates+=("${pf86}/Go/bin/go.exe")
  fi
  candidates+=(
    "/mnt/c/Program Files/Go/bin/go.exe"
    "/c/Program Files/Go/bin/go.exe"
    "/c/Program Files (x86)/Go/bin/go.exe"
  )
  local c
  for c in "${candidates[@]}"; do
    if path_exists "${c}"; then
      echo "${c}"
      return 0
    fi
  done
  return 1
}

pf_exe_path() {
  local root="$1"
  echo "${root}/core/cli/pf/pf.exe"
}

resolve_pf() {
  local root="$1"
  PF_CMD=()
  if [[ -n "${PF:-}" ]]; then
    # shellcheck disable=SC2206
    PF_CMD=(${PF})
    return 0
  fi
  local pf_exe
  pf_exe="$(pf_exe_path "${root}")"
  if path_exists "${pf_exe}"; then
    PF_CMD=("${pf_exe}")
    return 0
  fi
  local go_bin
  if ! go_bin="$(resolve_go_bin)"; then
    echo "go not found; install Go or build core/cli/pf/pf.exe (set PF=...)" >&2
    return 1
  fi
  if ! path_exists "${pf_exe}"; then
    (cd "${root}/core/cli/pf" && "${go_bin}" build -o pf.exe .) || return 1
  fi
  if path_exists "${pf_exe}"; then
    PF_CMD=("${pf_exe}")
    return 0
  fi
  PF_CMD=("${go_bin}" -C "${root}/core/cli/pf" run .)
  return 0
}

run_pf() {
  if [[ ${#PF_CMD[@]} -eq 0 ]]; then
    echo "run_pf: call resolve_pf or ensure_pf first" >&2
    return 1
  fi
  "${PF_CMD[@]}" "$@"
}

# ensure_pf builds pf.exe when Go is available; otherwise reuses an existing pf.exe.
ensure_pf() {
  local root="$1"
  local pf_exe
  pf_exe="$(pf_exe_path "${root}")"
  local go_bin
  if go_bin="$(resolve_go_bin)"; then
    (cd "${root}/core/cli/pf" && "${go_bin}" build -o pf.exe .) || return 1
    PF_CMD=("${pf_exe}")
    return 0
  fi
  if path_exists "${pf_exe}"; then
    echo "warning: go not found; using existing ${pf_exe}" >&2
    PF_CMD=("${pf_exe}")
    return 0
  fi
  echo "go not found and ${pf_exe} is missing; install Go or build pf.exe" >&2
  return 1
}

# rebuild_pf is an alias for ensure_pf (always attempts build when Go is present).
rebuild_pf() {
  ensure_pf "$1"
}
