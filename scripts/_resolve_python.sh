# shellcheck shell=bash
# Resolve a working Python interpreter (Git Bash on Windows often has a broken python3 store stub).

python_runs() {
  local bin="$1"
  command -v "${bin}" >/dev/null 2>&1 || return 1
  "${bin}" -c "import sys" >/dev/null 2>&1
}

resolve_python() {
  if [[ -n "${PYTHON:-}" ]]; then
    if python_runs "${PYTHON}"; then
      echo "${PYTHON}"
      return 0
    fi
    echo "PYTHON=${PYTHON} is not runnable" >&2
    return 1
  fi
  local candidates=(python3 python)
  case "$(uname -s 2>/dev/null || true)" in
    MINGW*|MSYS*|CYGWIN*)
      candidates=(python python3)
      ;;
  esac
  local c
  for c in "${candidates[@]}"; do
    if python_runs "${c}"; then
      echo "${c}"
      return 0
    fi
  done
  echo "python or python3 required (install Python or set PYTHON=...)" >&2
  return 1
}

run_materialize_admission_cases() {
  local root="$1"
  local py
  py="$(resolve_python)" || return 1
  PCS_BENCHMARK_QUIET=1 "${py}" "${root}/scripts/materialize-admission-benchmark-cases.py" --quiet
}
