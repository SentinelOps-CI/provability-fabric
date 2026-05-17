$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Bundle = Join-Path $Root "tests\pcs\fixtures\labtrust\science_claim_bundle.certified.json"
$Out = Join-Path $Root "tests\pcs\fixtures\labtrust\signed_science_claim_bundle.json"
$PfRoot = Join-Path $Root "core\cli\pf"
$PfExe = Join-Path $PfRoot "pf.exe"
if (-not (Get-Command go -ErrorAction SilentlyContinue)) { throw "go required" }
Push-Location $PfRoot; go build -o pf.exe .; Pop-Location
$env:PF_SOURCE_COMMIT = if ($env:PF_SOURCE_COMMIT) { $env:PF_SOURCE_COMMIT } else { "cccccccccccccccccccccccccccccccccccccccc" }
$env:PF_DETERMINISTIC = "1"
$env:PCS_DETERMINISTIC = "1"
& $PfExe verify science-claim $Bundle
& $PfExe sign science-claim $Bundle --out $Out
& $PfExe inspect science-claim $Out --strict
Write-Host "OK: wrote $Out"
