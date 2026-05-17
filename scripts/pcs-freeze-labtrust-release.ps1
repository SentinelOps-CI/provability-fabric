# Freeze LabTrust + CertifyEdge release fixtures (Windows / when bash has no go on PATH).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Release = Join-Path $Root "tests\pcs\fixtures\labtrust-release"
$Labtrust = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$CertifiedSrc = Join-Path $Labtrust "examples\pcs_qc_release\release\science_claim_bundle.certified.json"
$Certified = Join-Path $Release "science_claim_bundle.certified.json"
$VR = Join-Path $Release "verification_result.json"
$Signed = Join-Path $Release "signed_science_claim_bundle.json"

if (-not (Test-Path $CertifiedSrc)) {
    throw "LabTrust release certified bundle not found: $CertifiedSrc"
}

New-Item -ItemType Directory -Force -Path $Release | Out-Null
Copy-Item -Force $CertifiedSrc $Certified
Write-Host "Copied certified bundle from LabTrust-Gym release"

$py = Get-Command python -ErrorAction SilentlyContinue
if (-not $py) { $py = Get-Command python3 -ErrorAction SilentlyContinue }
if (-not $py) { throw "python required for invalid fixture generation" }
& $py.Source (Join-Path $Root "scripts\pcs-freeze-labtrust-release-invalid.py") $Release

$PfRoot = Join-Path $Root "core\cli\pf"
$PfExe = Join-Path $PfRoot "pf.exe"
if (-not (Get-Command go -ErrorAction SilentlyContinue)) {
    throw "go required to build pf.exe for fixture freeze"
}
Push-Location $PfRoot
try { go build -o pf.exe . | Out-Null } finally { Pop-Location }
$Pf = $PfExe

if (-not $env:PF_SOURCE_COMMIT) { $env:PF_SOURCE_COMMIT = "cccccccccccccccccccccccccccccccccccccccc" }
$env:PF_DETERMINISTIC = if ($env:PF_DETERMINISTIC) { $env:PF_DETERMINISTIC } else { "1" }
$env:PCS_DETERMINISTIC = if ($env:PCS_DETERMINISTIC) { $env:PCS_DETERMINISTIC } else { "1" }

& $Pf verify science-claim $Certified --out $VR
& $Pf sign science-claim $Certified --out $Signed
& $Pf inspect science-claim $Signed --strict
& $Pf validate verification-result $VR
& $Pf validate signed-science-claim $Signed

$PcsCore = if ($env:PCS_CORE_PATH) { $env:PCS_CORE_PATH } else { Join-Path $Parent "pcs-core" }
$PcsPy = Join-Path ([System.IO.Path]::GetFullPath($PcsCore)) "python"
if (Test-Path $PcsPy) {
    $env:PYTHONPATH = "$(Join-Path $PcsPy 'pcs_core');$PcsPy"
    python -m pcs_core.cli validate $Certified
    python -m pcs_core.cli validate $VR
    python -m pcs_core.cli validate $Signed
}

Write-Host "OK: labtrust-release fixtures frozen under $Release"
