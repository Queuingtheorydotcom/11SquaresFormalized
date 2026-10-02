[CmdletBinding()]
param(
    [ValidateSet(0, 1)][int]$Worker = 0,
    [ValidateRange(1, 16)][int]$MaxParallel = 2,
    [string]$Python,
    [switch]$Help
)

if ($Help) {
    Write-Output 'Run the assigned Windows proof worker using the shared plan.'
    Write-Output 'Worker 0 is machine-1; worker 1 is machine-2. No downloads or uploads.'
    Write-Output 'Private logs: .verification/distributed/runs/'
    exit 0
}

$ErrorActionPreference = 'Stop'
$workerExit = 1
$workerRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$workerLog = Join-Path $workerRoot '.verification/distributed/launcher-error.log'
try {
    . (Join-Path $PSScriptRoot 'distributed_env.ps1')
    $workerPython = Resolve-DistributedPython -Python $Python
    Push-Location -LiteralPath $workerRoot
    try {
        Write-Output ('Starting machine-{0}; preparing the shared source and compiler checks.' -f ($Worker + 1))
        Write-Output 'This preparation may take several minutes. Keep the computer awake.'
        & $workerPython -B -u scripts/distributed_worker.py run --worker $Worker --max-parallel $MaxParallel --resume-after-stop 2>> $workerLog
        $workerExit = $LASTEXITCODE
    } finally { Pop-Location }
} catch {
    $workerLogDirectory = Split-Path -Parent $workerLog
    if (Test-Path -LiteralPath $workerLogDirectory -PathType Container) {
        $_ | Out-String | Add-Content -LiteralPath $workerLog
    }
    Write-Output 'Worker could not start. See private .verification/distributed/launcher-error.log.'
}
exit $workerExit
