# Run PCS release admission benchmarks for all workflows (pcs-bench consumable artifacts).
param(
    [string]$Registry = "",
    [string]$OutRoot = ""
)

$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root

if (-not $Registry) {
    if ($env:PCS_BENCHMARK_REGISTRY) {
        $Registry = $env:PCS_BENCHMARK_REGISTRY
    } elseif ($env:PCS_CORE_PATH -and (Test-Path (Join-Path $env:PCS_CORE_PATH "examples\artifact_registry.valid.json"))) {
        $Registry = Join-Path $env:PCS_CORE_PATH "examples\artifact_registry.valid.json"
    } elseif (Test-Path (Join-Path $Root "..\pcs-core\examples\artifact_registry.valid.json")) {
        $Registry = (Resolve-Path (Join-Path $Root "..\pcs-core\examples\artifact_registry.valid.json")).Path
    } else {
        $Registry = Join-Path $Root "tests\pcs\fixtures\labtrust-release\artifact_registry.json"
    }
}

if (-not $OutRoot) {
    if ($env:PCS_BENCHMARK_OUT) {
        $OutRoot = $env:PCS_BENCHMARK_OUT
    } else {
        $OutRoot = Join-Path $Root "benchmark_runs"
    }
}
New-Item -ItemType Directory -Force -Path $OutRoot | Out-Null

if (Get-Command python -ErrorAction SilentlyContinue) {
    python (Join-Path $Root "scripts\materialize-admission-benchmark-cases.py")
} elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
    python3 (Join-Path $Root "scripts\materialize-admission-benchmark-cases.py")
} else {
    throw "python or python3 required to materialize benchmark cases"
}

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
        throw "go or core/cli/pf/pf.exe required; install Go, build pf.exe, or set PF=..."
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
    if ($LASTEXITCODE -ne 0) { throw "pf failed: $($Remaining -join ' ')" }
}

$Suites = @('labtrust_qc_release', 'tool_use_safety', 'computation_reproducibility', 'formal_trust_kernel')
$Failed = 0
foreach ($Suite in $Suites) {
    $Out = Join-Path $OutRoot "${Suite}_admission"
    Write-Host "==> pf benchmark admission --cases benchmarks/admission/$Suite"
    try {
        Invoke-Pf benchmark admission `
            --cases "benchmarks/admission/$Suite" `
            --registry $Registry `
            --out "benchmark_runs/${Suite}_admission"
    } catch {
        Write-Host $_
        $Failed++
    }
}

if ($Failed -ne 0) {
    Write-Error "admission benchmark: $Failed/$($Suites.Count) workflow suites failed"
}
Write-Host "OK: admission benchmarks wrote artifacts under $OutRoot"
