# PF segment: verify/sign into release-run/ from LabTrust certified handoff only.
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Run = if ($env:PCS_RELEASE_RUN) { $env:PCS_RELEASE_RUN } else { Join-Path $Root "release-run" }
$Labtrust = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$CertifiedSrc = Join-Path $Labtrust "examples\pcs_qc_release\release\science_claim_bundle.certified.json"
$HandoffSrc = Join-Path $Labtrust "examples\pcs_qc_release\release\pf_handoff.json"
$Certified = Join-Path $Run "science_claim_bundle.certified.json"
$VR = Join-Path $Run "verification_result.json"
$Signed = Join-Path $Run "signed_science_claim_bundle.json"

New-Item -ItemType Directory -Force -Path $Run | Out-Null
if (-not (Test-Path $CertifiedSrc)) {
    throw "LabTrust certified handoff not found: $CertifiedSrc"
}
if (-not (Test-Path $HandoffSrc)) {
    throw "LabTrust pf_handoff.json not found: $HandoffSrc"
}

Push-Location $Root
try { $env:PF_SOURCE_COMMIT = (git rev-parse HEAD).Trim() } finally { Pop-Location }
$env:PF_RELEASE_MODE = "1"
if (-not $env:PF_DETERMINISTIC) { $env:PF_DETERMINISTIC = "1" }

Copy-Item -Force $CertifiedSrc $Certified
Write-Host "== PF release-run: certified bundle from LabTrust handoff =="

$PfRoot = Join-Path $Root "core\cli\pf"
Push-Location $PfRoot
go build -o pf.exe .
Pop-Location
$Pf = Join-Path $PfRoot "pf.exe"

& $Pf verify science-claim $Certified --release-mode --out $VR
& $Pf sign science-claim $Certified --release-mode --handoff $HandoffSrc --out $Signed
& $Pf inspect science-claim $Signed --strict

python (Join-Path $Root "scripts\pcs-release-run-validate.py") $Run
Write-Host "OK: PF artifacts in $Run (pf_commit=$($env:PF_SOURCE_COMMIT))"
