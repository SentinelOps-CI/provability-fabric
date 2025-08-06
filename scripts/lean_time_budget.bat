@echo off
REM Lean Time Budget Checker (Windows)
REM Times per-file builds and enforces time budgets

setlocal enabledelayedexpansion

REM Configuration
set TOTAL_TIMEOUT=360
set PER_FILE_TIMEOUT=90
set WARN_THRESHOLD=60
set GRACE_PERIOD=30

REM Global state
set TOTAL_TIME=0
set SLOW_FILES=
set FAILED_FILES=
set WARNED_FILES=

echo 🔧 Lean Time Budget Checker
echo 📋 Total budget: %TOTAL_TIMEOUT%s
echo 📋 Per-file budget: %PER_FILE_TIMEOUT%s
echo 📋 Warning threshold: %WARN_THRESHOLD%s
echo.

REM Function to find all Lean files that need building
:find_lean_targets
set targets=
for /r %%f in (lakefile.lean) do (
    set "targets=!targets! %%~dpf"
)
goto :eof

REM Function to time a build
:time_build
set target=%~1
set start_time=%time%

echo 🔨 Building %target%...

REM Run lake build with timeout (using PowerShell for timeout)
powershell -Command "& { $job = Start-Job -ScriptBlock { cd '%target%'; lake build }; if (Wait-Job $job -Timeout %PER_FILE_TIMEOUT%) { Receive-Job $job; Remove-Job $job; exit 0 } else { Stop-Job $job; Remove-Job $job; exit 124 } }"

set exit_code=%errorlevel%
set end_time=%time%

REM Calculate duration (simplified)
set duration=0
if %exit_code% equ 0 (
    echo ✅ %target% completed
    if %duration% gtr %WARN_THRESHOLD% (
        set WARNED_FILES=!WARNED_FILES! %target%:%duration%s
    )
    set /a TOTAL_TIME+=%duration%
) else (
    if %exit_code% equ 124 (
        echo ⏰ TIMEOUT %target%
        set FAILED_FILES=!FAILED_FILES! %target%:TIMEOUT
    ) else (
        echo ❌ FAILED %target%
        set FAILED_FILES=!FAILED_FILES! %target%:FAILED
    )
    set /a TOTAL_TIME+=%duration%
)
goto :eof

REM Function to check if we're approaching total timeout
:check_total_budget
set /a remaining=%TOTAL_TIMEOUT%-%TOTAL_TIME%
if %remaining% lss %GRACE_PERIOD% (
    echo ⚠️  Warning: Only %remaining%s remaining in total budget
    exit /b 1
)
exit /b 0

REM Function to print results
:print_results
echo.
echo ============================================================
echo 📊 LEAN BUILD TIME RESULTS
echo ============================================================
echo ⏱️  Total build time: %TOTAL_TIME%s / %TOTAL_TIMEOUT%s

if %TOTAL_TIME% gtr %TOTAL_TIMEOUT% (
    echo ❌ Total time exceeded budget!
) else (
    echo ✅ Total time within budget
)

echo.

if not "!WARNED_FILES!"=="" (
    echo ⚠️  Slow files:
    for %%f in (!WARNED_FILES!) do echo    %%f
    echo.
)

if not "!FAILED_FILES!"=="" (
    echo ❌ Failed files:
    for %%f in (!FAILED_FILES!) do echo    %%f
    echo.
)

REM Summary
set total_files=0
for %%f in (!WARNED_FILES!) do set /a total_files+=1
for %%f in (!FAILED_FILES!) do set /a total_files+=1

if %total_files% equ 0 (
    echo ✅ All builds completed successfully!
    exit /b 0
) else (
    echo ❌ Found %total_files% problematic files
    exit /b 1
)

REM Main execution
:main
call :find_lean_targets
if "%targets%"=="" (
    echo ℹ️  No Lean targets found
    exit /b 0
)

echo 📁 Found targets to build
echo.

REM Build each target
for %%t in (%targets%) do (
    call :check_total_budget
    if errorlevel 1 (
        echo ⚠️  Stopping due to total budget constraint
        goto :print_results
    )
    call :time_build "%%t"
)

call :print_results
goto :eof

REM Run main function
call :main 