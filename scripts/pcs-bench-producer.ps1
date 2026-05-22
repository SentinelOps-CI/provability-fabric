# PF pcs-bench producer gate (Windows fallback when bash is unavailable).
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

if (Get-Command pcs-bench -ErrorAction SilentlyContinue) {
    pcs-bench validate-ingest --input $Ingest --pcs-core $PcsCore
} elseif (Get-Command pcs -ErrorAction SilentlyContinue) {
    pcs validate $Ingest
} else {
    go run ./tools/pcs-validate --benchmark-bundle $Out --pcs-core $PcsCore
}
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
Write-Host "OK: pcs-bench producer ingest at $Ingest"
