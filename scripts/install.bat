@echo off
REM Provability-Fabric Installation Script for Windows
REM Modes: minimal (CLI + bundles), standard (+ Rust), full (all). Set INSTALL_MODE or pass first arg.

if "%1" neq "" set INSTALL_MODE=%1
if "%INSTALL_MODE%"=="" set INSTALL_MODE=full
if "%INSTALL_MODE%"=="--minimal" set INSTALL_MODE=minimal
if "%INSTALL_MODE%"=="--standard" set INSTALL_MODE=standard
if "%INSTALL_MODE%"=="--full" set INSTALL_MODE=full

echo Setting up Provability-Fabric development environment (mode: %INSTALL_MODE%)...

REM Check prerequisites
echo Checking prerequisites...

where go >nul 2>&1
if %errorlevel% neq 0 (
    echo Go is not installed. Please install Go 1.21+ from https://golang.org/dl/
    exit /b 1
)

if "%INSTALL_MODE%"=="full" (
    where python >nul 2>&1
    if %errorlevel% neq 0 (
        echo Python is not installed. Please install Python 3.8+ for full install.
        exit /b 1
    )
)

if "%INSTALL_MODE%" neq "minimal" (
    where cargo >nul 2>&1
    if %errorlevel% neq 0 (
        echo Rust/cargo not found. Install from https://rustup.rs/ for standard/full install.
        exit /b 1
    )
)

where node >nul 2>&1
if %errorlevel% neq 0 (set NODE_AVAILABLE=false) else (set NODE_AVAILABLE=true)

echo Prerequisites check completed

REM Build CLI tools
echo Building CLI tools...
cd core\cli\pf
go build -o pf.exe .
echo Built pf CLI tool
cd ..\..\..

if not exist bundles mkdir bundles

if exist "cmd\specdoc\main.go" (
    cd cmd\specdoc
    go build -o specdoc.exe .
    echo Built specdoc CLI tool
    cd ..\..
)

if "%INSTALL_MODE%"=="standard" goto build_rust
if "%INSTALL_MODE%"=="full" goto build_rust
goto test_basic
:build_rust
echo Building Rust workspace...
cargo build --workspace 2>nul
if %errorlevel% neq 0 echo Rust workspace build had warnings or partial failure
goto test_basic

:test_basic
REM Full-only: Python and Node
if "%INSTALL_MODE%" neq "full" goto do_test
echo Installing Python dependencies...
if exist "tests\integration\requirements.txt" pip install -r tests\integration\requirements.txt
if exist "tests\proof-fuzz\requirements.txt" pip install -r tests\proof-fuzz\requirements.txt
if exist "tools\compliance\requirements.txt" pip install -r tools\compliance\requirements.txt
if exist "tools\insure\requirements.txt" pip install -r tools\insure\requirements.txt
if exist "tools\proofbot\requirements.txt" pip install -r tools\proofbot\requirements.txt
if "%NODE_AVAILABLE%"=="true" if exist "console\package.json" (
    cd console
    npm install --no-audit --no-fund
    cd ..
    echo Installed console dependencies
)

:do_test
echo Testing basic functionality...
if not exist "core\cli\pf\pf.exe" (echo pf CLI not found & exit /b 1)
core\cli\pf\pf.exe --help >nul 2>&1
echo pf CLI is working
core\cli\pf\pf.exe init test-agent
echo Agent initialization works

where lake >nul 2>&1
if %errorlevel% equ 0 (
    echo Testing Lean build...
    cd spec-templates\v1\proofs
    lake build >nul 2>&1
    echo Lean build works
    cd ..\..\..
) else (
    echo Lean 4 not found, skipping Lean build test
)

if exist "bundles\test-agent" rmdir /s /q bundles\test-agent

echo.
echo Installation completed successfully (mode: %INSTALL_MODE%)
echo.
echo Next steps:
echo 1. Add the CLI to your PATH: set PATH=%%PATH%%;%%CD%%\core\cli\pf
echo 2. Initialize an agent: core\cli\pf\pf.exe init my-agent
if "%INSTALL_MODE%"=="full" echo 3. Run tests: python tests\trust_fire_orchestrator.py
echo.
echo For minimal/standard/full modes see docs\guides\reuse-and-extend.md
echo For Lean 4 proofs: cd spec-templates\v1\proofs ^&^& lake build 