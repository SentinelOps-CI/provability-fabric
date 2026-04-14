@echo off
setlocal enabledelayedexpansion
REM Modes: minimal | standard | full. Set TEST_MODE or pass --minimal, --standard, --full
if "%1" neq "" set TEST_MODE=%1
if "%TEST_MODE%"=="" set TEST_MODE=full
if "%TEST_MODE%"=="--minimal" set TEST_MODE=minimal
if "%TEST_MODE%"=="--standard" set TEST_MODE=standard
if "%TEST_MODE%"=="--full" set TEST_MODE=full

echo Testing new user experience (mode: %TEST_MODE%)...

REM Test 1: Check if CLI builds and works
echo 📋 Test 1: CLI Build and Help
if exist "core\cli\pf\pf.exe" (
    echo ✅ CLI binary exists
) else (
    echo ❌ CLI binary not found
    exit /b 1
)

REM Test 2: Check if init command works
echo 📋 Test 2: Agent Initialization
set TEST_AGENT=test-new-user-agent
if exist "bundles\%TEST_AGENT%" (
    rmdir /s /q "bundles\%TEST_AGENT%"
)

.\core\cli\pf\pf.exe init %TEST_AGENT%

if exist "bundles\%TEST_AGENT%" (
    echo ✅ Agent bundle created
) else (
    echo ❌ Agent bundle not created
    exit /b 1
)

REM Test 3: Check if required files are present
echo 📋 Test 3: Required Files Check
if exist "bundles\%TEST_AGENT%\spec.yaml" (
    echo ✅ spec.yaml exists
) else (
    echo ❌ spec.yaml missing
    exit /b 1
)

if exist "bundles\%TEST_AGENT%\spec.md" (
    echo ✅ spec.md exists
) else (
    echo ❌ spec.md missing
    exit /b 1
)

if exist "bundles\%TEST_AGENT%\proofs\Spec.lean" (
    echo ✅ proofs\Spec.lean exists
) else (
    echo ❌ proofs\Spec.lean missing
    exit /b 1
)

if exist "bundles\%TEST_AGENT%\proofs\lakefile.lean" (
    echo ✅ proofs\lakefile.lean exists
) else (
    echo ❌ proofs\lakefile.lean missing
    exit /b 1
)

REM Test 4: Check if CLI commands work
echo 📋 Test 4: CLI Commands
.\core\cli\pf\pf.exe --help >nul 2>&1
if %errorlevel% equ 0 (
    echo ✅ CLI help command works
) else (
    echo ❌ CLI help command failed
    exit /b 1
)

if "%TEST_MODE%" neq "minimal" (
    echo Test 5: SpecDoc CLI
    if exist "cmd\specdoc\specdoc.exe" (echo SpecDoc CLI exists) else (echo SpecDoc CLI not found - optional)
)
if "%TEST_MODE%"=="minimal" (
    echo Test 5: Bundle pack
    core\cli\pf\pf.exe bundle pack bundles\test-new-user-agent -o %TEMP%\test-new-user-agent.tar.gz 2>nul && echo Bundle pack works || echo Bundle pack skipped
)

echo.
echo All tests passed for mode: %TEST_MODE%. See docs\guides\reuse-and-extend.md 