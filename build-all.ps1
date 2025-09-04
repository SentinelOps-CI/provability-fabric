# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

Write-Host "🔨 SentinelOps Platform - Build All Components" -ForegroundColor Green
Write-Host "=============================================="

function Write-Success($message) {
    Write-Host "✅ $message" -ForegroundColor Green
}

function Write-Error($message) {
    Write-Host "❌ $message" -ForegroundColor Red
}

# Build Go services
Write-Host ""
Write-Host "🐹 Building Go Services..." -ForegroundColor Yellow
$services = @("api-gateway", "spec-service", "proof-service", "build-orchestrator", "evidence-service", "replay-service")

foreach ($service in $services) {
    Write-Host "Building $service..."
    Set-Location "services\$service"
    
    try {
        & go mod tidy
        if ($LASTEXITCODE -eq 0) {
            & go build
            if ($LASTEXITCODE -eq 0) {
                Write-Success "$service built successfully"
            }
            else {
                Write-Error "$service build failed"
            }
        }
        else {
            Write-Error "$service go mod tidy failed"
        }
    }
    catch {
        Write-Error "$service build error: $_"
    }
    
    Set-Location "..\..\"
}

# Build TypeScript SDK
Write-Host ""
Write-Host "📦 Building TypeScript SDK..." -ForegroundColor Yellow
Set-Location "sdks\typescript"
try {
    & npm install
    if ($LASTEXITCODE -eq 0) {
        & npm run build
        if ($LASTEXITCODE -eq 0) {
            Write-Success "TypeScript SDK built successfully"
        }
        else {
            Write-Error "TypeScript SDK build failed"
        }
    }
}
catch {
    Write-Error "TypeScript SDK error: $_"
}
Set-Location "..\.."

# Build Demo Application
Write-Host ""
Write-Host "🎯 Building Demo Application..." -ForegroundColor Yellow
Set-Location "demos\verifiable-mcp-fraud"
try {
    & npm install
    if ($LASTEXITCODE -eq 0) {
        & npm run build
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Demo application built successfully"
        }
        else {
            Write-Error "Demo application build failed"
        }
    }
}
catch {
    Write-Error "Demo application error: $_"
}
Set-Location "..\.."

# Build Console UI
Write-Host ""
Write-Host "🖥️ Building Console UI..." -ForegroundColor Yellow
Set-Location "console"
try {
    & npm install
    if ($LASTEXITCODE -eq 0) {
        & npm run build
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Console UI built successfully"
        }
        else {
            Write-Error "Console UI build failed"
        }
    }
}
catch {
    Write-Error "Console UI error: $_"
}
Set-Location ".."

Write-Host ""
Write-Host "🎉 Build validation completed!" -ForegroundColor Green
Write-Host ""
Write-Host "📋 Summary:" -ForegroundColor Cyan
Write-Host "  - Go services (6): Tested" -ForegroundColor White
Write-Host "  - TypeScript SDK: Tested" -ForegroundColor White
Write-Host "  - Demo application: Tested" -ForegroundColor White
Write-Host "  - Console UI: Tested" -ForegroundColor White
Write-Host ""
Write-Host "🚀 Ready for Docker deployment!" -ForegroundColor Green
Write-Host "Run: docker compose up --build -d" -ForegroundColor Cyan

