@echo off
REM Provability Fabric CLI wrapper — run from repository root: pf verify science-claim ...
cd /d "%~dp0core\cli\pf"
go run . %*
