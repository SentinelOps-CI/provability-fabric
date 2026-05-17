# Atomically promote release-run/ PF artifacts to provability-fabric fixtures and pcs-core.
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Run = if ($env:PCS_RELEASE_RUN) { $env:PCS_RELEASE_RUN } else { Join-Path $Root "release-run" }
$PfFixtures = Join-Path $Root "tests\pcs\fixtures\labtrust-release"
$PcsCoreRelease = Join-Path $(if ($env:PCS_CORE_PATH) { $env:PCS_CORE_PATH } else { Join-Path $Parent "pcs-core" }) "examples\labtrust-release"

$Required = @(
    "science_claim_bundle.certified.json",
    "verification_result.json",
    "signed_science_claim_bundle.json"
)
foreach ($f in $Required) {
    if (-not (Test-Path (Join-Path $Run $f))) {
        throw "missing $(Join-Path $Run $f) (run scripts/pcs-release-run-pf.ps1 first)"
    }
}

python (Join-Path $Root "scripts\pcs-release-run-validate.py") $Run

Push-Location $Root
try { $PfCommit = (git rev-parse HEAD).Trim() } finally { Pop-Location }
$Manifest = Join-Path $Run "RELEASE_FIXTURE_MANIFEST.json"
if (Test-Path $Manifest) {
    python -c @"
import json, pathlib, sys
p, commit = pathlib.Path(r'$Manifest'), r'$PfCommit'
m = json.loads(p.read_text(encoding='utf-8'))
m['provability_fabric_commit'] = commit
m['pf_source_commit'] = commit
p.write_text(json.dumps(m, indent=2) + '\n', encoding='utf-8')
"@
}

function Promote-To($dest) {
    New-Item -ItemType Directory -Force -Path $dest | Out-Null
    foreach ($f in $Required) {
        Copy-Item -Force (Join-Path $Run $f) (Join-Path $dest $f)
    }
    if (Test-Path $Manifest) {
        Copy-Item -Force $Manifest (Join-Path $dest "FIXTURE_MANIFEST.json")
    }
    Write-Host "promoted PF artifacts -> $dest"
}

Promote-To $PfFixtures

$PfManifest = Join-Path $PfFixtures "FIXTURE_MANIFEST.json"
if (Test-Path $PfManifest) {
    python -c @"
import json, pathlib
p, commit = pathlib.Path(r'$PfManifest'), r'$PfCommit'
m = json.loads(p.read_text(encoding='utf-8'))
m['pf_source_commit'] = commit
m['regenerate'] = 'make freeze-pcs-labtrust-release'
p.write_text(json.dumps(m, indent=2) + '\n', encoding='utf-8')
"@
}

if (Test-Path $PcsCoreRelease) {
    foreach ($f in $Required) {
        Copy-Item -Force (Join-Path $Run $f) (Join-Path $PcsCoreRelease $f)
    }
    python (Join-Path $Root "scripts\pcs-sync-pcs-core-release.py") $Run $PcsCoreRelease $PfCommit
}

python (Join-Path $Root "scripts\pcs-freeze-labtrust-release-invalid.py") $PfFixtures
Write-Host "OK: atomic promote from $Run"
