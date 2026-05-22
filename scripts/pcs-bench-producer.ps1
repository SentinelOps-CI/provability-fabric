# PF pcs-bench producer gate (Windows fallback).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $Root

python scripts/materialize-admission-benchmark-cases.py
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

$PcsCore = $env:PCS_CORE_PATH
if (-not $PcsCore -and (Test-Path (Join-Path $Root "..\pcs-core\schemas"))) {
    $PcsCore = (Resolve-Path (Join-Path $Root "..\pcs-core")).Path
}
if (-not $PcsCore) {
    Write-Error "PCS_CORE_PATH or ../pcs-core with schemas/ is required"
}

$Registry = $env:PCS_BENCHMARK_REGISTRY
if (-not $Registry) {
    $candidate = Join-Path $PcsCore "examples\artifact_registry.valid.json"
    if (Test-Path $candidate) { $Registry = (Resolve-Path $candidate).Path }
    else { $Registry = (Resolve-Path "tests\pcs\fixtures\labtrust-release\artifact_registry.json").Path }
}

$Out = if ($env:PCS_BENCHMARK_OUT) { $env:PCS_BENCHMARK_OUT } else { Join-Path $Root "benchmark_runs\labtrust_admission" }
New-Item -ItemType Directory -Force -Path $Out | Out-Null

Push-Location (Join-Path $Root "core\cli\pf")
go run . benchmark admission `
  --cases (Join-Path $Root "benchmarks\admission\labtrust_qc_release") `
  --registry $Registry `
  --out $Out `
  --validate `
  --validate-pcs-core-output $PcsCore `
  --json-summary
if ($LASTEXITCODE -ne 0) { Pop-Location; exit $LASTEXITCODE }
Pop-Location

$Ingest = Join-Path $Out "pcs_bench_ingest.v0.json"
if (-not (Test-Path $Ingest)) { Write-Error "missing $Ingest" }

python -m pip install -q -e (Join-Path $PcsCore "python")
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

python (Join-Path $Root "scripts\validate-pf-pcs-bench-ingest.py") `
  --ingest $Ingest `
  --bundle-dir $Out `
  --pcs-core $PcsCore `
  --release-grade
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

python (Join-Path $Root "scripts\pcs-bench-producer-contract-check.py") `
  --ingest $Ingest `
  --bundle-dir $Out
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

if (Get-Command pcs -ErrorAction SilentlyContinue) {
    pcs validate $Ingest
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

Write-Host "OK: pcs-bench producer ingest at $Ingest"
