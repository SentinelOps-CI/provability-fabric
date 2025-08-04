@echo off
REM Provability-Fabric Installation Script for Windows
REM This script sets up the development environment for new users

echo 🚀 Setting up Provability-Fabric development environment...

REM Check prerequisites
echo 📋 Checking prerequisites...

REM Check Go
where go >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ Go is not installed. Please install Go 1.21+ from https://golang.org/dl/
    exit /b 1
)

REM Check Python
where python >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ Python is not installed. Please install Python 3.8+
    exit /b 1
)

REM Check Node.js (optional)
where node >nul 2>&1
if %errorlevel% neq 0 (
    echo ⚠️  Node.js not found. UI components will be skipped.
    set NODE_AVAILABLE=false
) else (
    set NODE_AVAILABLE=true
)

echo ✅ Prerequisites check completed

REM Build CLI tools
echo 🔨 Building CLI tools...

cd core\cli\pf
go build -o pf.exe .
echo ✅ Built pf CLI tool

cd ..\..\..

REM Build specdoc CLI (optional)
if exist "cmd\specdoc\main.go" (
    cd cmd\specdoc
    go build -o specdoc.exe .
    echo ✅ Built specdoc CLI tool
    cd ..\..
) else (
    echo ⚠️  specdoc CLI not found, skipping
)

REM Install Python dependencies (if requirements.txt files exist)
echo 🐍 Installing Python dependencies...

if exist "tests\integration\requirements.txt" (
    pip install -r tests\integration\requirements.txt
    echo ✅ Installed integration test dependencies
)

if exist "tests\proof-fuzz\requirements.txt" (
    pip install -r tests\proof-fuzz\requirements.txt
    echo ✅ Installed proof-fuzz dependencies
)

if exist "tools\compliance\requirements.txt" (
    pip install -r tools\compliance\requirements.txt
    echo ✅ Installed compliance tool dependencies
)

if exist "tools\insure\requirements.txt" (
    pip install -r tools\insure\requirements.txt
    echo ✅ Installed insurance tool dependencies
)

if exist "tools\proofbot\requirements.txt" (
    pip install -r tools\proofbot\requirements.txt
    echo ✅ Installed proofbot dependencies
)

REM Install Node.js dependencies (if available)
if "%NODE_AVAILABLE%"=="true" if exist "marketplace\ui\package.json" (
    echo 📦 Installing Node.js dependencies...
    cd marketplace\ui
    npm install
    cd ..\..
    echo ✅ Installed UI dependencies
)

REM Test basic functionality
echo 🧪 Testing basic functionality...

REM Test pf CLI
if exist "core\cli\pf\pf.exe" (
    core\cli\pf\pf.exe --help >nul 2>&1
    echo ✅ pf CLI is working
) else (
    echo ❌ pf CLI not found
    exit /b 1
)

REM Test agent initialization
core\cli\pf\pf.exe init test-agent
echo ✅ Agent initialization works

REM Test Lean build (if Lean is available)
where lake >nul 2>&1
if %errorlevel% equ 0 (
    echo 🔍 Testing Lean build...
    cd spec-templates\v1\proofs
    lake build >nul 2>&1
    echo ✅ Lean build works
    cd ..\..\..
) else (
    echo ⚠️  Lean 4 not found, skipping Lean build test
)

REM Clean up test agent
if exist "bundles\test-agent" rmdir /s /q bundles\test-agent

echo.
echo 🎉 Installation completed successfully!
echo.
echo Next steps:
echo 1. Add the CLI to your PATH: set PATH=%%PATH%%;%%CD%%\core\cli\pf
echo 2. Initialize an agent: core\cli\pf\pf.exe init my-agent
echo 3. Run tests: python tests\trust_fire_orchestrator.py
echo.
echo For Lean 4 proofs, install Lean and run: cd spec-templates\v1\proofs ^&^& lake build 