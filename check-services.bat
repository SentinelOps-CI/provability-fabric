@echo off
echo ====================================
echo Provability-Fabric Service Status
echo ====================================
echo.

echo Checking services...
echo.

REM Check Admin Interface
curl -s http://localhost:9000 >nul 2>&1
if %errorlevel% == 0 (
    echo [✓] Admin Interface       - RUNNING on port 9000
) else (
    echo [✗] Admin Interface       - NOT RUNNING on port 9000
)

REM Check Documentation
curl -s http://127.0.0.1:8002 >nul 2>&1
if %errorlevel% == 0 (
    echo [✓] Documentation         - RUNNING on port 8002
) else (
    echo [✗] Documentation         - NOT RUNNING on port 8002
)

REM Check Marketplace UI
curl -s http://localhost:3000 >nul 2>&1
if %errorlevel% == 0 (
    echo [✓] Marketplace UI        - RUNNING on port 3000
) else (
    echo [✗] Marketplace UI        - NOT RUNNING on port 3000
)

REM Check Ledger Service
curl -s http://localhost:4000 >nul 2>&1
if %errorlevel% == 0 (
    echo [✓] Ledger GraphQL        - RUNNING on port 4000
) else (
    echo [✗] Ledger GraphQL        - NOT RUNNING on port 4000
)

echo.
echo ====================================
echo Service Status Check Complete
echo ====================================
echo.
pause
