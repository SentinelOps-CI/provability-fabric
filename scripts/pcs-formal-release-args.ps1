# Emit pf CLI flags for Lean trust-envelope artifacts when present in a release fixture dir.
param([string]$ReleaseDir)

if (-not $ReleaseDir) {
    throw "usage: pcs-formal-release-args.ps1 <release_fixture_dir>"
}
$po = Join-Path $ReleaseDir "proof_obligation.v0.json"
$lc = Join-Path $ReleaseDir "lean_check_result.v0.json"
$args = @()
if (Test-Path $po) { $args += @("--proof-obligations", $po) }
if (Test-Path $lc) { $args += @("--lean-check-result", $lc) }
$args
