# PCS v0.1 full clean-checkout chain (delegates to LabTrust-Gym when present).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Labtrust = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$Chain = Join-Path $Labtrust "examples\pcs_qc_release\scripts\run_pcs_v01_clean_chain.ps1"

if (-not (Test-Path $Chain)) {
    $PfPs1 = Join-Path $Root "scripts\pcs-pf-clean-chain.ps1"
    $Release = Join-Path $Root "tests\pcs\fixtures\labtrust-release"
    if (-not (Test-Path (Join-Path $Release "science_claim_bundle.certified.json"))) {
        throw "LabTrust-Gym chain script not found: $Chain`nClone LabTrust-Gym beside provability-fabric or set LABTRUST_GYM_ROOT."
    }
    & $PfPs1 $Release
    $Sm = if ($env:SCIENTIFIC_MEMORY_ROOT) { $env:SCIENTIFIC_MEMORY_ROOT } else { Join-Path $Parent "scientific-memory" }
    if (Test-Path (Join-Path $Sm "justfile")) {
        Push-Location $Sm
        try {
            just pcs-import-bundle (Join-Path $Release "signed_science_claim_bundle.json")
            just pcs-render-claim claim-pcs-qc-release-v0.1
        } finally { Pop-Location }
    }
    Write-Host "OK: PF + optional SM segment (full chain requires LabTrust-Gym)"
    exit 0
}

if (-not $env:PCS_DETERMINISTIC) { $env:PCS_DETERMINISTIC = "1" }
$PrevEap = $ErrorActionPreference
$ErrorActionPreference = "Continue"
try {
    & $Chain @args
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
} finally {
    $ErrorActionPreference = $PrevEap
}
