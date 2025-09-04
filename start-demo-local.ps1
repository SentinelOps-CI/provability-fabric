# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors
# Local Demo Startup Script (without Docker)

Write-Host "🎬 Starting SentinelOps Platform Demo (Local Mode)" -ForegroundColor Green
Write-Host "=================================================="

Write-Host ""
Write-Host "⚠️  This script starts services locally without Docker" -ForegroundColor Yellow
Write-Host "   Make sure you have PostgreSQL and Redis running separately"
Write-Host ""

# Set environment variables
$env:PORT_API_GATEWAY = "8000"
$env:PORT_SPEC_SERVICE = "8001"
$env:PORT_PROOF_SERVICE = "8002"
$env:PORT_BUILD_SERVICE = "8003"
$env:PORT_EVIDENCE_SERVICE = "8004"
$env:PORT_REPLAY_SERVICE = "8005"
$env:PORT_RUNTIME_SERVICE = "8006"

$env:SPEC_SERVICE_URL = "http://localhost:8001"
$env:PROOF_SERVICE_URL = "http://localhost:8002"
$env:BUILD_SERVICE_URL = "http://localhost:8003"
$env:EVIDENCE_SERVICE_URL = "http://localhost:8004"
$env:REPLAY_SERVICE_URL = "http://localhost:8005"
$env:RUNTIME_SERVICE_URL = "http://localhost:8006"

$env:DATABASE_URL = "postgres://sentinelops:sentinelops_password@localhost:5432/sentinelops"
$env:REDIS_URL = "redis://localhost:6379"

Write-Host "🔧 Environment configured" -ForegroundColor Green

# Function to start service in background
function Start-Service($name, $path, $port) {
    Write-Host "Starting $name on port $port..."
    Set-Location $path
    
    # Start the service in a new PowerShell window
    $command = "& '.\$name.exe'; Read-Host 'Press Enter to close'"
    Start-Process powershell -ArgumentList "-NoExit", "-Command", $command -WindowStyle Normal
    
    Set-Location $PSScriptRoot
    Start-Sleep -Seconds 2
}

Write-Host ""
Write-Host "🚀 Starting services..." -ForegroundColor Yellow

# Start Go services (assuming they're already built)
Start-Service "api-gateway" "services\api-gateway" "8000"
Start-Service "spec-service" "services\spec-service" "8001"
Start-Service "proof-service" "services\proof-service" "8002"
Start-Service "build-orchestrator" "services\build-orchestrator" "8003"
Start-Service "evidence-service" "services\evidence-service" "8004"
Start-Service "replay-service" "services\replay-service" "8005"

Write-Host ""
Write-Host "🌐 Starting web applications..." -ForegroundColor Yellow

# Start Console UI
Write-Host "Starting Console UI on port 3000..."
Set-Location "console"
Start-Process powershell -ArgumentList "-NoExit", "-Command", "npm start; Read-Host 'Press Enter to close'" -WindowStyle Normal
Set-Location ".."

# Start Demo Application
Write-Host "Starting Demo Application on port 3001..."
Set-Location "demos\verifiable-mcp-fraud"
$env:PORT = "3001"
Start-Process powershell -ArgumentList "-NoExit", "-Command", "npm start; Read-Host 'Press Enter to close'" -WindowStyle Normal
Set-Location "..\.."

Write-Host ""
Write-Host "✅ Demo environment starting!" -ForegroundColor Green
Write-Host ""
Write-Host "🌐 Access Points:" -ForegroundColor Cyan
Write-Host "  Console UI:     http://localhost:3000" -ForegroundColor White
Write-Host "  API Gateway:    http://localhost:8000" -ForegroundColor White
Write-Host "  Demo App:       http://localhost:3001" -ForegroundColor White
Write-Host ""
Write-Host "⚠️  Note: Make sure PostgreSQL and Redis are running locally" -ForegroundColor Yellow
Write-Host "   PostgreSQL: localhost:5432 (user: sentinelops, password: sentinelops_password)" -ForegroundColor Gray
Write-Host "   Redis: localhost:6379" -ForegroundColor Gray
Write-Host ""
Write-Host "🎯 Demo Flow:" -ForegroundColor Cyan
Write-Host "  1. Open Console UI and go to Policies tab" -ForegroundColor White
Write-Host "  2. See the fraud detection policy compiled and deployed" -ForegroundColor White
Write-Host "  3. Go to Runtime tab to monitor live metrics" -ForegroundColor White
Write-Host "  4. Go to Evidence tab to see CERT-V1 certificates" -ForegroundColor White
Write-Host "  5. Run replays to verify 99.9%+ low-view equality" -ForegroundColor White
Write-Host "  6. Download compliance packets" -ForegroundColor White

