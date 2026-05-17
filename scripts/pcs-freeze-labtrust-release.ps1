# Freeze LabTrust release fixtures via atomic release-run promotion (Windows).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
& (Join-Path $PSScriptRoot "pcs-release-run-pf.ps1")
& (Join-Path $PSScriptRoot "pcs-release-run-promote.ps1")
Write-Host "OK: freeze-pcs-labtrust-release (release-run) from $Root"
