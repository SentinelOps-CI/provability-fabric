# Provability Fabric segment of PCS v0.1 clean-checkout chain.
param([string]$Workdir = "")

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
if (-not $Workdir) { $Workdir = Join-Path $Root "tests\pcs\fixtures\labtrust-release" }
$Workdir = (Resolve-Path $Workdir).Path

$Certified = Join-Path $Workdir "science_claim_bundle.certified.json"
$VR = Join-Path $Workdir "verification_result.json"
$Signed = Join-Path $Workdir "signed_science_claim_bundle.json"

$PfRoot = Join-Path $Root "core\cli\pf"
$PfExe = Join-Path $PfRoot "pf.exe"
if (Test-Path $PfExe) {
    $Pf = $PfExe
} elseif (Get-Command go -ErrorAction SilentlyContinue) {
    Push-Location $PfRoot
    try { go build -o pf.exe . | Out-Null } finally { Pop-Location }
    $Pf = $PfExe
} else {
    throw "go or core/cli/pf/pf.exe required; set PF_BIN"
}

$PcsCore = if ($env:PCS_CORE_PATH) { $env:PCS_CORE_PATH } else { Join-Path (Split-Path $Root -Parent) "pcs-core" }
$PcsCore = [System.IO.Path]::GetFullPath($PcsCore)
$PcsPy = Join-Path $PcsCore "python"
if (-not (Test-Path $PcsPy)) { throw "pcs-core not found at $PcsCore (set PCS_CORE_PATH)" }
$env:PYTHONPATH = "$(Join-Path $PcsPy 'pcs_core');$PcsPy"
$Pcs = "python -m pcs_core.cli"

if (-not (Test-Path $Certified)) { throw "missing certified bundle: $Certified" }
if (-not $env:PF_SOURCE_COMMIT) {
    Push-Location $Root
    try { $env:PF_SOURCE_COMMIT = (git rev-parse HEAD 2>$null) } catch { }
    Pop-Location
    if (-not $env:PF_SOURCE_COMMIT) { $env:PF_SOURCE_COMMIT = "cccccccccccccccccccccccccccccccccccccccc" }
}

function Step([string]$Msg) { Write-Host "== $Msg ==" }

Step "Provability Fabric: verify"
& $Pf verify science-claim $Certified --out $VR
Step "pcs-core: validate verification_result"
Invoke-Expression "$Pcs validate `"$VR`""
Step "Provability Fabric: sign"
& $Pf sign science-claim $Certified --out $Signed
Step "pcs-core: validate signed bundle"
Invoke-Expression "$Pcs validate `"$Signed`""
Step "Provability Fabric: inspect"
& $Pf inspect science-claim $Signed --strict
Write-Host "OK: PF clean-chain segment completed in $Workdir"
