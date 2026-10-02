<#
.SYNOPSIS
Run the local proof-verification handoff with private, resumable diagnostics.
#>
[CmdletBinding(PositionalBinding = $false)]
param(
    [string]$Python,
    [ValidateRange(1, 2147483647)]
    [int]$Workers = 4,
    [ValidateRange(1, 95)]
    [int]$MemoryPercent = 95,
    [switch]$SkipBenchmark,
    [switch]$ResumeAfterStop,
    [string]$StopFile,
    [switch]$Help
)

if ($Help) {
    Write-Output @'
Run RUN_FORMALIZATION.cmd by double-clicking it, with no arguments.
It explicitly resumes after a deliberate stop: the runner clears only its
default stop-request file after acquiring the ownership locks.
For options, run this PowerShell script directly:
  .\scripts\run_complete_verification.ps1 -Workers 4 -MemoryPercent 95
  .\scripts\run_complete_verification.ps1 -Python "path\to\python.exe"

Options:
  -Python PATH       Use a specific Python 3.11-or-newer interpreter.
  -Workers N         Maximum proof workers requested from the runner (default 4).
  -MemoryPercent N   Soft memory ceiling, from 1 through 95 (default 95).
  -SkipBenchmark     Skip the comparison and use the runner's serial fallback.
  -StopFile PATH     Use a stop-request file inside .verification.
  -ResumeAfterStop   Explicitly clear the runner's default stop request.
  -Help             Show this help without starting Python or Lean.

Latest run: .verification\run\latest.json
Private run folder: runner.log, benchmark.log, verifier.log, finalizer.log,
                   summary.json, and summary.txt
Launcher errors: .verification\run\launcher-error.log

This launcher makes no global settings changes and performs no GitHub writes.
'@
    exit 0
}

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$containerRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$privateRunRoot = Join-Path $containerRoot '.verification\run'
$originalLocation = Get-Location
$exitCode = 1

function Find-FormalizationPython {
    param([string]$Override, [string]$Root)
    $candidates = [Collections.Generic.List[string]]::new()
    if ($Override) {
        $candidates.Add($Override)
    } else {
        if ($env:FORMALIZATION_PYTHON) {
            $candidates.Add($env:FORMALIZATION_PYTHON)
        }
        $candidates.Add((Join-Path $Root 'work\tooling\python\python.exe'))
        if ($env:USERPROFILE) {
            $candidates.Add((Join-Path $env:USERPROFILE '.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'))
        }
        if ($env:LOCALAPPDATA) {
            $installRoot = Join-Path $env:LOCALAPPDATA 'Programs\Python'
            if (Test-Path -LiteralPath $installRoot -PathType Container) {
                foreach ($installation in Get-ChildItem -LiteralPath $installRoot -Directory | Sort-Object Name -Descending) {
                    $candidates.Add((Join-Path $installation.FullName 'python.exe'))
                }
            }
        }
        foreach ($name in @('python3.exe', 'python.exe')) {
            $application = Get-Command -Name $name -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
            if ($application) { $candidates.Add($application.Source) }
        }
    }
    foreach ($candidate in $candidates | Select-Object -Unique) {
        # Skip Windows Store aliases, which may open the Store instead of Python.
        if ($candidate -like '*\Microsoft\WindowsApps\*') { continue }
        if ([IO.Path]::GetExtension($candidate) -ne '.exe') { continue }
        if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) { continue }
        $resolved = (Resolve-Path -LiteralPath $candidate).ProviderPath
        try {
            & $resolved -I -B -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 11) else 1)' >$null 2>$null
            if ($LASTEXITCODE -eq 0) { return $resolved }
        } catch {
            # A failed candidate is never evaluated as shell text or disclosed.
        }
    }
    throw 'A working Python 3.11-or-newer interpreter was not found. Use -Python.'
}

try {
    Set-Location -LiteralPath $containerRoot
    New-Item -ItemType Directory -Force -Path $privateRunRoot | Out-Null
    $environmentScript = Join-Path $containerRoot '.verification\env.ps1'
    if (-not (Test-Path -LiteralPath $environmentScript -PathType Leaf)) {
        throw 'The local environment file is missing; restore the prepared checkout environment first.'
    }
    . $environmentScript
    # Never inherit verbose transport diagnostics into the saved run logs.
    foreach ($entry in Get-ChildItem Env:GIT_TRACE* -ErrorAction SilentlyContinue) {
        Remove-Item -LiteralPath ('Env:' + $entry.Name) -ErrorAction SilentlyContinue
    }
    foreach ($name in @('GIT_CURL_VERBOSE', 'CURL_VERBOSE', 'CURL_TRACE', 'SSLKEYLOGFILE')) {
        Remove-Item -LiteralPath ('Env:' + $name) -ErrorAction SilentlyContinue
    }
    $env:PYTHONUTF8 = '1'
    $env:PYTHONDONTWRITEBYTECODE = '1'
    $pythonExecutable = Find-FormalizationPython -Override $Python -Root $containerRoot
    $runner = Join-Path $PSScriptRoot 'run_complete_verification.py'
    if (-not (Test-Path -LiteralPath $runner -PathType Leaf)) {
        throw 'The verification runner is missing from this checkout.'
    }
    $runnerArguments = @('-B', $runner, '--workers', [string]$Workers,
                         '--memory-percent', [string]$MemoryPercent)
    if ($SkipBenchmark) { $runnerArguments += '--skip-benchmark' }
    if ($ResumeAfterStop) { $runnerArguments += '--resume-after-stop' }
    if ($StopFile) {
        $stopPath = if ([IO.Path]::IsPathRooted($StopFile)) {
            [IO.Path]::GetFullPath($StopFile)
        } else {
            [IO.Path]::GetFullPath((Join-Path $containerRoot $StopFile))
        }
        $rootPrefix = $containerRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
        if (-not $stopPath.StartsWith($rootPrefix, [StringComparison]::OrdinalIgnoreCase)) {
            throw 'The stop-request file must be inside this checkout.'
        }
        $runnerArguments += @('--stop-file', $stopPath)
    }
    Write-Host 'Starting the local formalization run. Accepted work can be resumed.'
    Write-Host 'Latest run and private log location: .verification\run\latest.json'
    & $pythonExecutable @runnerArguments
    $exitCode = $LASTEXITCODE
} catch {
    try {
        New-Item -ItemType Directory -Force -Path $privateRunRoot | Out-Null
        [IO.File]::WriteAllText((Join-Path $privateRunRoot 'launcher-error.log'),
            ($_ | Out-String), [Text.UTF8Encoding]::new($false))
    } catch {
        # Report only the stable relative location, never a private machine path.
    }
    Write-Host 'The launcher could not finish. Private details: .verification\run\launcher-error.log'
    Write-Host 'If Python is missing, retry this script with -Python "path\to\python.exe".'
    $exitCode = 1
} finally {
    Set-Location -LiteralPath $originalLocation.Path
}
Write-Host ('Run finished with exit code ' + $exitCode + '.')
Write-Host 'Latest run details: .verification\run\latest.json'
exit $exitCode
