# Freeze LabTrust + CertifyEdge release fixtures (Windows).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
$Parent = Split-Path -Parent $Root
$Release = Join-Path $Root "tests\pcs\fixtures\labtrust-release"
$PcsCore = if ($env:PCS_CORE_PATH) { $env:PCS_CORE_PATH } else { Join-Path $Parent "pcs-core" }
$Labtrust = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$CertifiedSrc = Join-Path $Labtrust "examples\pcs_qc_release\release\science_claim_bundle.certified.json"
$Certified = Join-Path $Release "science_claim_bundle.certified.json"
$VR = Join-Path $Release "verification_result.json"
$Signed = Join-Path $Release "signed_science_claim_bundle.json"
$Manifest = Join-Path $Release "FIXTURE_MANIFEST.json"

$Forbidden = @(
    "0000000000000000000000000000000000000000",
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "cccccccccccccccccccccccccccccccccccccccc",
    "dddddddddddddddddddddddddddddddddddddddd",
    "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
)

Push-Location $Root
try { $env:PF_SOURCE_COMMIT = (git rev-parse HEAD).Trim() } finally { Pop-Location }
if ($Forbidden -contains $env:PF_SOURCE_COMMIT) {
    throw "PF_SOURCE_COMMIT is a forbidden placeholder: $($env:PF_SOURCE_COMMIT)"
}
$env:PF_RELEASE_MODE = "1"
$env:PF_DETERMINISTIC = if ($env:PF_DETERMINISTIC) { $env:PF_DETERMINISTIC } else { "1" }

Copy-Item -Force $CertifiedSrc $Certified
python (Join-Path $Root "scripts\pcs-freeze-labtrust-release-invalid.py") $Release

$PfRoot = Join-Path $Root "core\cli\pf"
Push-Location $PfRoot; go build -o pf.exe .; Pop-Location
$Pf = Join-Path $PfRoot "pf.exe"

& $Pf verify science-claim $Certified --release-mode --out $VR
& $Pf sign science-claim $Certified --release-mode --out $Signed
& $Pf inspect science-claim $Signed --strict
& $Pf validate verification-result $VR
& $Pf validate signed-science-claim $Signed

python -c "import json,pathlib;p=pathlib.Path(r'$Manifest');m=json.loads(p.read_text(encoding='utf-8')) if p.exists() else {};m['pf_source_commit']='$($env:PF_SOURCE_COMMIT)';m['regenerate']='make freeze-pcs-labtrust-release';m.pop('deterministic_env',None);p.write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')"

$PcsCoreRelease = Join-Path $PcsCore "examples\labtrust-release"
if (Test-Path $PcsCoreRelease) {
    python (Join-Path $Root "scripts\pcs-sync-pcs-core-release.py") $Release $PcsCoreRelease $env:PF_SOURCE_COMMIT
}
Write-Host "OK: labtrust-release fixtures frozen (pf_source_commit=$($env:PF_SOURCE_COMMIT))"
