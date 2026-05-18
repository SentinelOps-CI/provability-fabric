# PCS RC fixture lock tests (Windows).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
if (-not $env:PCS_CORE_PATH) {
    $env:PCS_CORE_PATH = (Join-Path (Split-Path -Parent $Root) "pcs-core")
}
Push-Location (Join-Path $Root "adapters\pcs")
try {
    go test -count=1 -run "PFLabtrustReleaseFixtureMatchesPCSCoreRC|PFSignedBundleRCIdentity|TestPFAcceptsValidHandoffManifest|TestReleaseChainResultStatusProofCheckedOnValidChain|TestPFHashMatchesPCSCoreSignedBundleVector|TestReleaseModeRequiresHandoff|TestReleaseModeRequiresRegistry|TestReleaseChainResultContainsRegistryChecks" ./...
} finally {
    Pop-Location
}
