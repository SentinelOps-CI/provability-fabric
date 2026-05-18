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

function Get-PfCommand {
    if ($env:PF) {
        $pf = $env:PF.Trim()
        $goRunSuffix = ' run .'
        if ($pf.StartsWith('go -C ') -and $pf.EndsWith($goRunSuffix)) {
            $dir = $pf.Substring(6, $pf.Length - 6 - $goRunSuffix.Length).Trim().Trim('"')
            return @('go', '-C', $dir, 'run', '.')
        }
        return $pf -split '\s+'
    }
    if (-not (Get-Command go -ErrorAction SilentlyContinue)) {
        if (Test-Path $PfExe) { return @($PfExe) }
        throw "go or core/cli/pf/pf.exe required; set PF=..."
    }
    Push-Location $PfRoot
    try {
        & go build -o pf.exe .
        if ($LASTEXITCODE -ne 0) { throw "go build core/cli/pf failed" }
    } finally {
        Pop-Location
    }
    if (-not (Test-Path $PfExe)) { throw "missing $PfExe after build" }
    return @($PfExe)
}

$PfCmd = @(Get-PfCommand)

function Invoke-Pf {
    param([Parameter(ValueFromRemainingArguments = $true)][string[]]$Remaining)
    if ($PfCmd.Count -ge 5 -and $PfCmd[0] -eq 'go' -and $PfCmd[1] -eq '-C' -and $PfCmd[3] -eq 'run') {
        & $PfCmd[0] -C $PfCmd[2] run . @Remaining
    } elseif ($PfCmd.Count -eq 1) {
        & $PfCmd[0] @Remaining
    } else {
        & $PfCmd[0] @($PfCmd[1..($PfCmd.Count - 1)] + $Remaining)
    }
    if ($LASTEXITCODE -ne 0) {
        throw "pf failed (exit $LASTEXITCODE): $($Remaining -join ' ')"
    }
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
    try { $env:PF_SOURCE_COMMIT = (git rev-parse HEAD 2>$null).Trim() } catch { }
    Pop-Location
}
if (-not $env:PF_RELEASE_MODE) { $env:PF_RELEASE_MODE = "1" }
if (-not $env:PF_ADMISSION_PROFILE) { $env:PF_ADMISSION_PROFILE = "labtrust_qc_release" }

$ReleaseFixtures = Join-Path $Root "tests\pcs\fixtures\labtrust-release"
$Handoff = if ($env:PF_HANDOFF) { $env:PF_HANDOFF } else { Join-Path $ReleaseFixtures "handoff_to_pf.json" }
$Registry = if ($env:PF_REGISTRY) { $env:PF_REGISTRY } else { Join-Path $ReleaseFixtures "artifact_registry.json" }

function Step([string]$Msg) { Write-Host "== $Msg ==" }

Step "Provability Fabric: verify"
Invoke-Pf verify science-claim $Certified --release-mode --handoff $Handoff --registry $Registry --out $VR
Step "pcs-core: validate verification_result"
Invoke-Expression "$Pcs validate `"$VR`""
if ($LASTEXITCODE -ne 0) { throw "pcs-core validate verification_result failed" }
Step "Provability Fabric: sign"
Invoke-Pf sign science-claim $Certified --release-mode --handoff $Handoff --registry $Registry --out $Signed
Step "pcs-core: validate signed bundle"
Invoke-Expression "$Pcs validate `"$Signed`""
if ($LASTEXITCODE -ne 0) { throw "pcs-core validate signed bundle failed" }
Step "Provability Fabric: inspect"
Invoke-Pf inspect science-claim $Signed --strict
Write-Host "OK: PF clean-chain segment completed in $Workdir"
