@echo off
REM SPDX-License-Identifier: Apache-2.0
REM Copyright 2025 Provability-Fabric Contributors

echo 🔍 Checking for duplicate Lean definitions across bundles...

REM Configuration
set DUPLICATES_FOUND=0

REM Find all Lean files in bundles
echo 📁 Scanning Lean files in bundles...
for /f "tokens=*" %%f in ('dir /s /b bundles\*.lean ^| findstr /v ".lake"') do (
    echo   - %%f
)

REM Check for identical definition bodies using git grep
echo 🔍 Checking for identical definition bodies using git grep...

REM Common patterns that should not be duplicated
set PATTERNS=inductive Action where def budget_ok def total_spend theorem example_theorem

for %%p in (%PATTERNS%) do (
    echo   Checking pattern: %%p
    
    REM Find all occurrences
    for /f "tokens=*" %%f in ('git grep -l "%%p" -- "bundles/*/proofs/*.lean" 2^>nul') do (
        echo     Found in: %%f
    )
)

REM Check for imports from core DSL
echo 🔍 Checking for proper imports from core DSL...

for /f "tokens=*" %%f in ('dir /s /b bundles\*.lean ^| findstr /v ".lake"') do (
    findstr /c:"import Fabric" "%%f" >nul
    if !errorlevel! equ 0 (
        echo ✅ %%f imports from core DSL
    ) else (
        echo ⚠️  %%f does not import from core DSL
    )
)

REM Check for duplicate core definitions
echo 🔍 Checking for duplicate core definitions...

REM Check for duplicate Action definitions
for /f "tokens=*" %%f in ('findstr /s /l "inductive Action" bundles\*.lean 2^>nul') do (
    echo ❌ Found duplicate Action definitions in: %%f
    set DUPLICATES_FOUND=1
)

REM Check for duplicate budget_ok definitions
for /f "tokens=*" %%f in ('findstr /s /l "def budget_ok" bundles\*.lean 2^>nul') do (
    echo ❌ Found duplicate budget_ok definitions in: %%f
    set DUPLICATES_FOUND=1
)

REM Final report
echo.
if %DUPLICATES_FOUND% equ 0 (
    echo ✅ No duplicate definitions found!
    echo ✅ All bundles properly use core DSL
    exit /b 0
) else (
    echo ❌ Duplicate definitions found!
    echo.
    echo 💡 Recommendations:
    echo   1. Move duplicate definitions to core/lean-libs/ActionDSL.lean
    echo   2. Import from core DSL in bundle files
    echo   3. Keep only agent-specific logic in bundle files
    exit /b 1
) 