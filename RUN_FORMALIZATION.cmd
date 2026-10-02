@echo off
setlocal DisableDelayedExpansion
rem Double-click entry point: no command-line arguments are forwarded.
rem For options, invoke scripts\run_complete_verification.ps1 directly.
pushd "%~dp0"
if errorlevel 1 goto location_failed
echo Starting or resuming verification; previous stop request will be cleared.
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -NoLogo -NoProfile -ExecutionPolicy Bypass -File "scripts\run_complete_verification.ps1" -ResumeAfterStop
set "FORMALIZATION_EXIT=%ERRORLEVEL%"
popd
goto finished

:location_failed
echo Could not open the formalization folder.
set "FORMALIZATION_EXIT=1"

:finished
echo.
echo Latest run details: .verification\run\latest.json
echo Private logs are in the run folder named there.
echo Launcher errors, if any: .verification\run\launcher-error.log
echo This window will stay open until you press a key.
pause >nul
exit /b %FORMALIZATION_EXIT%
