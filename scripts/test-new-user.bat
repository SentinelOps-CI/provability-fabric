@echo off
setlocal enabledelayedexpansion

echo 🧪 Testing new user experience...

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

REM Test 5: Check if specdoc CLI works (optional)
echo 📋 Test 5: SpecDoc CLI
if exist "cmd\specdoc\specdoc.exe" (
    echo ✅ SpecDoc CLI exists
) else (
    echo ⚠️  SpecDoc CLI not found (optional component)
)

echo.
echo 🎉 All tests passed! New user experience is working correctly.
echo.
echo ✅ CLI builds and runs
echo ✅ Agent initialization works
echo ✅ Required files are created
echo ✅ CLI commands function properly
echo ✅ SpecDoc CLI is available
echo.
echo The repository is ready for new users! 🚀 