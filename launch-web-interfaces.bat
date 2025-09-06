@echo off
echo ====================================
echo Provability-Fabric Web Interface Launcher
echo ====================================
echo.

echo Starting Documentation Site (Port 8002)...
start /B cmd /c "mkdocs serve --dev-addr=127.0.0.1:8002"
timeout /t 2 /nobreak >nul

echo Starting Console UI (Port 3000)...
start /B cmd /c "cd console && npm start"
timeout /t 3 /nobreak >nul

echo Starting Ledger Service (Port 4000)...
start /B cmd /c "cd runtime/ledger && npm run dev:minimal"
timeout /t 2 /nobreak >nul

echo.
echo ====================================
echo Web Interfaces Launch Complete!
echo ====================================
echo.
echo Access URLs:
echo - Documentation:     http://127.0.0.1:8002
echo - Console UI:        http://localhost:3000
echo - Ledger GraphQL:    http://localhost:4000
echo.
echo Press any key to open Console UI...
pause >nul
start http://localhost:3000

echo.
echo Note: Services are running in background.
echo Use Ctrl+C in their respective windows to stop them.
pause
