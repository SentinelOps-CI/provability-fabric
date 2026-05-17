@echo off
setlocal
set "ROOT=%~dp0"
set "ROOT=%ROOT:~0,-1%"
if not defined PCS_CORE_PATH set "PCS_CORE_PATH=%ROOT%\..\pcs-core"
set "PY=%PCS_CORE_PATH%\python"
if not exist "%PY%\pcs_core\cli.py" (
  echo pcs-core not found at %PCS_CORE_PATH% >&2
  exit /b 2
)
set "PYTHONPATH=%PY%;%PYTHONPATH%"
python -m pcs_core.cli %*
