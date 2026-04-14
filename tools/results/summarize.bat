@echo off
REM Results Summarizer for Provability-Fabric Paper
REM This script generates a summary of verification results

echo {> results.json
echo   "commit": "> results.json

REM Get git commit hash
for /f "tokens=*" %%i in ('git rev-parse --short HEAD') do (
    echo %%i",>> results.json
)

echo   "proof": "> results.json

REM Check if Spec.olean was built
if exist "spec-templates\v1\proofs\.lake\build\lib\Spec.olean" (
    echo verified",>> results.json
) else (
    echo fail",>> results.json
)

echo   "bundle_id": "n/a",>> results.json
echo   "signature": "n/a",>> results.json
echo   "replay_drift": "n/a">> results.json
echo }>> results.json

echo Results written to results.json
type results.json
