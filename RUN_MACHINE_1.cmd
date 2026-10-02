@echo off
setlocal DisableDelayedExpansion
pushd "%~dp0"
if errorlevel 1 exit /b 1
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -NoLogo -NoProfile -ExecutionPolicy Bypass -File "scripts\distributed_run.ps1" -Worker 0 -MaxParallel 2
set "FORMALIZATION_EXIT=%ERRORLEVEL%"
popd
echo.
echo Private log pointer: .verification\distributed\latest-worker-00.json
echo Press any key to close this window.
pause >nul
exit /b %FORMALIZATION_EXIT%
