@echo off
echo ====================================
echo Provability-Fabric Web Interface Launcher
echo ====================================
echo.

echo Starting Admin Interface (Port 9000)...
start /B cmd /c "cd admin-interface && node server.js"
timeout /t 2 /nobreak >nul

echo Starting Documentation Site (Port 8002)...
start /B cmd /c "mkdocs serve --dev-addr=127.0.0.1:8002"
timeout /t 2 /nobreak >nul

echo Starting Marketplace UI (Port 3000)...
start /B cmd /c "cd marketplace/ui && npm start"
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
echo - Admin Dashboard:    http://localhost:9000
echo - Documentation:     http://127.0.0.1:8002
echo - Marketplace UI:    http://localhost:3000
echo - Ledger GraphQL:    http://localhost:4000
echo.
echo Press any key to open Admin Dashboard...
pause >nul
start http://localhost:9000

echo.
echo Note: Services are running in background.
echo Use Ctrl+C in their respective windows to stop them.
pause
