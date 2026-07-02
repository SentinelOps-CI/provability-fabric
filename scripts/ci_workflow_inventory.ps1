# ci_workflow_inventory.ps1 - PowerShell equivalent of ci_workflow_inventory.sh
#
# Usage:
#   scripts/ci_workflow_inventory.ps1 [-ListOnly] [-Markdown [FILE]]
#
# Requires: gh CLI authenticated for GitHub API queries.
# Exit 0 when all gated workflows have conclusion=success on the last main run.

param(
    [switch]$ListOnly,
    [switch]$Markdown,
    [string]$MarkdownFile = ""
)

$ErrorActionPreference = "Stop"

$RootDir = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$WfDir = Join-Path $RootDir ".github/workflows"
$Repo = if ($env:GITHUB_REPOSITORY) { $env:GITHUB_REPOSITORY } else { "SentinelOps-CI/provability-fabric" }
$Branch = if ($env:CI_INVENTORY_BRANCH) { $env:CI_INVENTORY_BRANCH } else { "main" }
$MissingUrl = "-"

if (-not (Get-Command gh -ErrorAction SilentlyContinue)) {
    Write-Error "gh CLI is required"
    exit 2
}

if ($Markdown -and -not $MarkdownFile) {
    $MarkdownFile = Join-Path $RootDir "docs/internal/ci-inventory-latest.md"
}

function Test-WorkflowHasPushOrSchedule {
    param([string]$FilePath)
    $content = Get-Content -Raw -Path $FilePath
    if ($content -match '(?m)^\s*(push|schedule):') { return $true }
    if ($content -match 'on:\s*\[.*\b(push|schedule)\b') { return $true }
    return $false
}

function Get-WorkflowTriggers {
    param([string]$FilePath)
    $content = Get-Content -Raw -Path $FilePath
    $triggers = @('push', 'pull_request', 'pull_request_target', 'schedule', 'release', 'workflow_dispatch', 'workflow_call', 'issue_comment') |
        Where-Object {
            $t = $_
            ($content -match "(?m)^\s*${t}:") -or ($content -match "on:\s*\[.*\b${t}\b")
        }
    if ($triggers.Count -eq 0) { return $MissingUrl }
    return ($triggers -join ', ')
}

function Get-LastMainRun {
    param([string]$WorkflowFile)
    try {
        $json = gh run list --repo $Repo --workflow $WorkflowFile --branch $Branch --limit 1 --json conclusion,status,url 2>$null
        if (-not $json) { return @{ Status = "no_run"; Url = $MissingUrl } }
        $runs = $json | ConvertFrom-Json
        if ($runs.Count -eq 0) { return @{ Status = "no_run"; Url = $MissingUrl } }
        $run = $runs[0]
        $status = if ($run.conclusion) { $run.conclusion } elseif ($run.status) { $run.status } else { "unknown" }
        $url = if ($run.url) { $run.url } else { $MissingUrl }
        return @{ Status = $status; Url = $url }
    } catch {
        return @{ Status = "no_run"; Url = $MissingUrl }
    }
}

$total = 0
$gated = 0
$green = 0
$red = 0
$unknown = 0
$failures = @()
$mdRows = @()

Write-Host "CI workflow inventory - repo=$Repo branch=$Branch"
Write-Host ("{0,-42} {1,-28} {2,-12} {3}" -f "WORKFLOW", "TRIGGERS", "STATUS", "URL")
Write-Host ("-" * 110)

$workflowFiles = @(
    Get-ChildItem -Path $WfDir -Filter *.yml -File -ErrorAction SilentlyContinue
    Get-ChildItem -Path $WfDir -Filter *.yaml -File -ErrorAction SilentlyContinue
) | Sort-Object Name

foreach ($wf in $workflowFiles) {
    $fname = $wf.Name
    $total++
    $triggers = Get-WorkflowTriggers -FilePath $wf.FullName
    $run = Get-LastMainRun -WorkflowFile $fname
    $status = $run.Status
    $url = $run.Url

    switch ($status) {
        "success" { $green++ }
        { $_ -in @("no_run", "unknown", "") } { $unknown++ }
        default { $red++ }
    }

    $isGated = Test-WorkflowHasPushOrSchedule -FilePath $wf.FullName
    $gateSuffix = ""
    $gatedFlag = "no"
    if ($isGated) {
        $gated++
        $gateSuffix = "*"
        $gatedFlag = "yes"
        if ($status -ne "success") {
            $failures += "$fname ($status)"
        }
    }

    Write-Host ("{0,-42} {1,-28} {2,-12} {3}" -f $fname, $triggers, "$status$gateSuffix", $url)
    $mdRows += [PSCustomObject]@{
        Workflow = $fname
        Triggers = $triggers
        Status   = $status
        Gated    = $gatedFlag
        Url      = $url
    }
}

Write-Host ""
Write-Host "Summary: total=$total gated(push/schedule)=$gated green=$green red=$red unknown=$unknown"

if ($Markdown) {
    $generatedAt = (Get-Date).ToUniversalTime().ToString("yyyy-MM-ddTHH:mm:ssZ")
    $sb = New-Object System.Text.StringBuilder
    [void]$sb.AppendLine("# CI workflow inventory (auto-generated)")
    [void]$sb.AppendLine("")
    [void]$sb.AppendLine("Generated: ${generatedAt} UTC")
    [void]$sb.AppendLine("Repository: ``$Repo`` branch ``$Branch``")
    [void]$sb.AppendLine("")
    [void]$sb.AppendLine("## Summary")
    [void]$sb.AppendLine("")
    [void]$sb.AppendLine("| Metric | Count |")
    [void]$sb.AppendLine("|--------|------:|")
    [void]$sb.AppendLine("| Total workflow files | $total |")
    [void]$sb.AppendLine("| Gated (push/schedule on main) | $gated |")
    [void]$sb.AppendLine("| Green (last run success) | $green |")
    [void]$sb.AppendLine("| Red (failure/cancelled/in progress) | $red |")
    [void]$sb.AppendLine("| No run / unknown | $unknown |")
    [void]$sb.AppendLine("")
    [void]$sb.AppendLine("## Workflows")
    [void]$sb.AppendLine("")
    [void]$sb.AppendLine("| Workflow | Triggers | Last status | Gated | URL |")
    [void]$sb.AppendLine("|----------|----------|-------------|-------|-----|")
    foreach ($row in $mdRows) {
        $displayStatus = $row.Status
        if ($row.Gated -eq "yes" -and $row.Status -ne "success") {
            $displayStatus = "**$($row.Status)**"
        }
        [void]$sb.AppendLine("| ``$($row.Workflow)`` | $($row.Triggers) | $displayStatus | $($row.Gated) | $($row.Url) |")
    }
    if ($failures.Count -gt 0) {
        [void]$sb.AppendLine("")
        [void]$sb.AppendLine("## Gated workflows not green")
        [void]$sb.AppendLine("")
        foreach ($f in $failures) {
            [void]$sb.AppendLine("- ``$f``")
        }
    }
    Set-Content -Path $MarkdownFile -Value $sb.ToString() -Encoding utf8
    Write-Host "Markdown report written to $MarkdownFile"
}

if ($ListOnly) {
    exit 0
}

if ($failures.Count -gt 0) {
    Write-Host ""
    Write-Host "Gated workflows not green on last $Branch run:" -ForegroundColor Red
    foreach ($f in $failures) {
        Write-Host "  - $f"
    }
    exit 1
}

exit 0
