<# Dot-source this file before distributed worker commands. Process scope only. #>
[CmdletBinding()]
param([switch]$Help)

if ($Help) {
    Write-Output 'Dot-source scripts/distributed_env.ps1 to scope runtime, cache, and temporary files to this checkout.'
    Write-Output 'No installation, download, or global configuration change is performed.'
    return
}

$distributedRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$distributedState = Join-Path $distributedRoot '.verification\distributed'

function New-DistributedDirectory {
    param([Parameter(Mandatory = $true)][string]$Path)
    $absolute = [IO.Path]::GetFullPath($Path)
    $prefix = $distributedRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
    if (-not $absolute.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw 'Distributed runtime directories must remain inside this checkout.'
    }
    $part = $absolute
    while ($part -and $part -ne $distributedRoot) {
        if (Test-Path -LiteralPath $part) {
            $item = Get-Item -LiteralPath $part -Force
            if (-not $item.PSIsContainer -or ($item.Attributes -band [IO.FileAttributes]::ReparsePoint)) {
                throw 'A distributed runtime directory is a file or redirected directory.'
            }
        }
        $part = [IO.Path]::GetDirectoryName($part)
    }
    New-Item -ItemType Directory -Force -Path $absolute | Out-Null
    return $absolute
}

$distributedState = New-DistributedDirectory $distributedState
$existingElan = Join-Path $distributedRoot 'work\tooling\elan'
$env:ELAN_HOME = if (Test-Path -LiteralPath $existingElan -PathType Container) {
    New-DistributedDirectory $existingElan
} else {
    New-DistributedDirectory (Join-Path $distributedState 'elan')
}
$env:TEMP = New-DistributedDirectory (Join-Path $distributedState 'tmp')
$env:TMP = $env:TEMP
$env:XDG_CACHE_HOME = New-DistributedDirectory (Join-Path $distributedState 'cache')
$env:MATHLIB_CACHE_DIR = New-DistributedDirectory (Join-Path $distributedState 'cache\mathlib')
$env:CURL_HOME = New-DistributedDirectory (Join-Path $distributedState 'cache\curl')
$env:PYTHONUTF8 = '1'
$env:PYTHONDONTWRITEBYTECODE = '1'
$env:GIT_TERMINAL_PROMPT = '0'
$elanBin = Join-Path $env:ELAN_HOME 'bin'
if (($env:Path -split ';') -notcontains $elanBin) { $env:Path = $elanBin + ';' + $env:Path }
$pin = (Get-Content -LiteralPath (Join-Path $distributedRoot 'lean-toolchain') -Raw).Trim()
if ($pin -notmatch '^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+$') { throw 'Invalid pinned Lean toolchain.' }
$env:ELAN_TOOLCHAIN = $pin

# Scoped Git exceptions cover only this checkout and its pinned packages.
# Repeated dot-sourcing retains inherited settings and never duplicates entries.
$configCount = 0
if ($env:GIT_CONFIG_COUNT -and -not [int]::TryParse($env:GIT_CONFIG_COUNT, [ref]$configCount)) {
    throw 'Invalid inherited process Git configuration count.'
}
if ($configCount -lt 0 -or $configCount -gt 1000) { throw 'Invalid process Git configuration count.' }
$safePaths = [Collections.Generic.List[string]]::new()
$safePaths.Add($distributedRoot)
$packageManifest = Get-Content -LiteralPath (Join-Path $distributedRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
foreach ($package in $packageManifest.packages) {
    if ($package.name -notmatch '^[A-Za-z0-9_-]+$') { throw 'Invalid pinned package name.' }
    $safePaths.Add((Join-Path $distributedRoot ('.lake\packages\' + $package.name)))
}
foreach ($safePath in $safePaths) {
    $normalized = $safePath.Replace('\', '/')
    $present = $false
    for ($index = 0; $index -lt $configCount; $index++) {
        if ([Environment]::GetEnvironmentVariable("GIT_CONFIG_KEY_$index", 'Process') -eq 'safe.directory' -and
            [Environment]::GetEnvironmentVariable("GIT_CONFIG_VALUE_$index", 'Process') -eq $normalized) {
            $present = $true
            break
        }
    }
    if (-not $present) {
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$configCount", 'safe.directory', 'Process')
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$configCount", $normalized, 'Process')
        $configCount++
    }
}
$env:GIT_CONFIG_COUNT = [string]$configCount
$env:FORMALIZATION_DISTRIBUTED_ROOT = $distributedRoot
foreach ($entry in Get-ChildItem Env:GIT_TRACE* -ErrorAction SilentlyContinue) {
    Remove-Item -LiteralPath ('Env:' + $entry.Name) -ErrorAction SilentlyContinue
}
foreach ($name in @('GIT_CURL_VERBOSE', 'CURL_VERBOSE', 'CURL_TRACE', 'SSLKEYLOGFILE')) {
    Remove-Item -LiteralPath ('Env:' + $name) -ErrorAction SilentlyContinue
}

function Resolve-DistributedPython {
    param([string]$Python)
    $candidates = [Collections.Generic.List[string]]::new()
    if ($Python) {
        $candidates.Add($Python)
    } else {
        if ($env:FORMALIZATION_PYTHON) { $candidates.Add($env:FORMALIZATION_PYTHON) }
        $candidates.Add((Join-Path $distributedRoot 'work\tooling\python\python.exe'))
        if ($env:USERPROFILE) {
            $candidates.Add((Join-Path $env:USERPROFILE '.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'))
        }
        foreach ($name in @('python.exe', 'python3.exe')) {
            $command = Get-Command $name -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
            if ($command) { $candidates.Add($command.Source) }
        }
    }
    foreach ($candidate in $candidates | Select-Object -Unique) {
        if ($candidate -like '*\Microsoft\WindowsApps\*' -or [IO.Path]::GetExtension($candidate) -ne '.exe') { continue }
        if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) { continue }
        $resolved = (Resolve-Path -LiteralPath $candidate).ProviderPath
        try {
            & $resolved -I -B -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 11) else 1)' >$null 2>$null
            if ($LASTEXITCODE -eq 0) { return $resolved }
        } catch { }
    }
    throw 'Python 3.11 or newer is required; provide -Python or FORMALIZATION_PYTHON.'
}
