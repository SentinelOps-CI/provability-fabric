@echo off
REM SPDX-License-Identifier: Apache-2.0
REM Copyright 2025 Provability-Fabric Contributors

echo 🔧 Vendoring mathlib for offline builds...

REM Configuration
set MATHLIB_VERSION=v4.7.0
set MATHLIB_COMMIT=b5eba595428809e96f3ed113bc7ba776c5f801ac
set VENDOR_DIR=vendor\mathlib

REM Create vendor directory
if not exist "%VENDOR_DIR%" mkdir "%VENDOR_DIR%"

REM Clone mathlib to vendor directory
echo 📥 Cloning mathlib %MATHLIB_VERSION% to %VENDOR_DIR%...
if not exist "%VENDOR_DIR%\.git" (
    git clone --depth 1 --branch %MATHLIB_VERSION% https://github.com/leanprover-community/mathlib4.git "%VENDOR_DIR%"
) else (
    echo ✅ Mathlib already exists in vendor directory
)

REM Verify the correct commit
cd "%VENDOR_DIR%"
for /f "tokens=*" %%i in ('git rev-parse HEAD') do set CURRENT_COMMIT=%%i
if not "%CURRENT_COMMIT%"=="%MATHLIB_COMMIT%" (
    echo ⚠️  Warning: Expected commit %MATHLIB_COMMIT%, got %CURRENT_COMMIT%
    echo 🔄 Checking out correct commit...
    git fetch origin %MATHLIB_VERSION%
    git checkout %MATHLIB_COMMIT%
)

REM Build mathlib to generate .olean files
echo 🔨 Building mathlib...
lake build

REM Create a lakefile.lean in the vendor directory
echo import Lake > lakefile.lean
echo open Lake DSL >> lakefile.lean
echo. >> lakefile.lean
echo package mathlib { >> lakefile.lean
echo   -- add package configuration options here >> lakefile.lean
echo } >> lakefile.lean
echo. >> lakefile.lean
echo @[default_target] >> lakefile.lean
echo lean_lib Mathlib { >> lakefile.lean
echo   -- add library configuration options here >> lakefile.lean
echo } >> lakefile.lean

cd ..\..

echo ✅ Mathlib vendored successfully!
echo 📁 Location: %VENDOR_DIR%
echo 🔗 Commit: %MATHLIB_COMMIT%
echo 🏷️  Version: %MATHLIB_VERSION% 