# PF segment: verify/sign into release-run/ from LabTrust certified handoff only.
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Run = if ($env:PCS_RELEASE_RUN) { $env:PCS_RELEASE_RUN } else { Join-Path $Root "release-run" }
$Labtrust = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$PcsCore = if ($env:PCS_CORE_PATH) { $env:PCS_CORE_PATH } else { Join-Path $Parent "pcs-core" }
$LtRelease = Join-Path $Labtrust "examples\pcs_qc_release\release"
$CertifiedSrc = Join-Path $LtRelease "science_claim_bundle.certified.json"
$Certified = Join-Path $Run "science_claim_bundle.certified.json"
$VR = Join-Path $Run "verification_result.json"
$Signed = Join-Path $Run "signed_science_claim_bundle.json"

function Resolve-PfHandoffPath {
    param([string]$ReleaseDir, [string]$PcsCoreRoot)
    $candidates = @(
        (Join-Path $ReleaseDir "handoff_to_pf.json"),
        (Join-Path $ReleaseDir "handoff_manifest.bundle_to_verifier.v0.json")
    )
    foreach ($p in $candidates) {
        if (Test-Path $p) { return $p }
    }
    if ($PcsCoreRoot) {
        $rc = @(
            (Join-Path $PcsCoreRoot "examples\labtrust-release\handoff_to_pf.json"),
            (Join-Path $PcsCoreRoot "examples\labtrust-release\handoff_manifest.bundle_to_verifier.v0.json")
        )
        foreach ($p in $rc) {
            if (Test-Path $p) { return $p }
        }
    }
    return $null
}

function Resolve-PfRegistryPath {
    param([string]$ReleaseDir, [string]$PcsCoreRoot, [string]$PfRoot)
    $candidates = @(
        (Join-Path $ReleaseDir "artifact_registry.json"),
        (Join-Path $ReleaseDir "artifact_registry.v0.json")
    )
    foreach ($p in $candidates) {
        if (Test-Path $p) { return $p }
    }
    $pcsReg = Join-Path $PcsCoreRoot "examples\artifact_registry.valid.json"
    if ($PcsCoreRoot -and (Test-Path $pcsReg)) { return $pcsReg }
    $pfReg = Join-Path $PfRoot "tests\pcs\fixtures\labtrust-release\artifact_registry.json"
    if (Test-Path $pfReg) { return $pfReg }
    return $null
}

New-Item -ItemType Directory -Force -Path $Run | Out-Null
if (-not (Test-Path $CertifiedSrc)) {
    throw "LabTrust certified handoff not found: $CertifiedSrc"
}
$HandoffSrc = Resolve-PfHandoffPath -ReleaseDir $LtRelease -PcsCoreRoot $PcsCore
if (-not $HandoffSrc) {
    throw "HandoffManifest.v0 not found under $LtRelease or $PcsCore\examples\labtrust-release"
}
$RegistrySrc = Resolve-PfRegistryPath -ReleaseDir $LtRelease -PcsCoreRoot $PcsCore -PfRoot $Root
if (-not $RegistrySrc) {
    throw "ArtifactRegistry.v0 not found for release-mode PF"
}

Push-Location $Root
try { $env:PF_SOURCE_COMMIT = (git rev-parse HEAD).Trim() } finally { Pop-Location }
$env:PF_RELEASE_MODE = "1"
if (-not $env:PF_ADMISSION_PROFILE) { $env:PF_ADMISSION_PROFILE = "labtrust_qc_release" }
if (-not $env:PF_DETERMINISTIC) { $env:PF_DETERMINISTIC = "1" }

Copy-Item -Force $CertifiedSrc $Certified
Write-Host "== PF release-run: certified bundle from LabTrust handoff =="

$PfRoot = Join-Path $Root "core\cli\pf"
Push-Location $PfRoot
go build -o pf.exe .
Pop-Location
$Pf = Join-Path $PfRoot "pf.exe"

& $Pf verify science-claim $Certified --release-mode --handoff $HandoffSrc --registry $RegistrySrc --out $VR
& $Pf sign science-claim $Certified --release-mode --handoff $HandoffSrc --registry $RegistrySrc --out $Signed
& $Pf inspect science-claim $Signed --strict

python (Join-Path $Root "scripts\pcs-release-run-validate.py") $Run
Write-Host "OK: PF artifacts in $Run (pf_commit=$($env:PF_SOURCE_COMMIT))"
