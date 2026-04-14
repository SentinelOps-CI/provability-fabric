@echo off
set REPO_ROOT=%PF_REPO_ROOT%
if "%REPO_ROOT%"=="" set REPO_ROOT=.
cd /d "%REPO_ROOT%"
python -m bench.swebench.guard.executor %*
