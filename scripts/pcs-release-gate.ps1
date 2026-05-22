# PCS release gate (Windows): mirrors make test-pcs-full + schema sync.
param(
    [string]$PcsCore = $env:PCS_CORE_PATH
)

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root

if (-not $PcsCore) {
    $sibling = Join-Path (Split-Path $Root -Parent) "pcs-core"
    if (Test-Path (Join-Path $sibling "schemas")) { $PcsCore = (Resolve-Path $sibling).Path }
}
if (-not $PcsCore) { throw "Set PCS_CORE_PATH to a pcs-core checkout" }
$env:PCS_CORE_PATH = $PcsCore

Write-Host "== sync schemas from pcs-core =="
bash scripts/pcs-schema-sync.sh "$PcsCore"
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

Write-Host "== make test-pcs-full =="
& make test-pcs-full
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

Write-Host "== demo-pcs + demo-pcs-release =="
& make demo-pcs
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& make demo-pcs-release
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

Write-Host "== pcs-v01-pf-chain =="
$env:PF_RELEASE_MODE = "1"
& make pcs-v01-pf-chain
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

Write-Host "OK: PCS release gate passed"
