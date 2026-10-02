<# Non-destructive Windows bootstrap. Network use requires explicit -Install. #>
[CmdletBinding()]
param([switch]$Install, [string]$Python, [switch]$Help)

if ($Help) {
    Write-Output @'
Windows distributed proof setup:
  .\scripts\distributed_setup.ps1                 Check local prerequisites only.
  .\scripts\distributed_setup.ps1 -Install        Restore pinned public prerequisites.
  .\scripts\distributed_setup.ps1 -Install -Python "path\to\python.exe"
Then dot-source .\scripts\distributed_env.ps1 before worker commands.

Only -Install permits downloads: pinned elan 4.2.3, the repository's Lean
toolchain, authenticated generated sources, and pinned mathlib dependencies.
Existing matching files are reused. No global Git, environment, or OS settings
are changed. An active verifier or distributed runner prevents setup.
Private diagnostics: .verification/distributed/setup.log
'@
    exit 0
}

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$ProgressPreference = 'SilentlyContinue'
$setupRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$setupLog = Join-Path $setupRoot '.verification\distributed\setup.log'
$setupLocks = [Collections.Generic.List[IO.FileStream]]::new()
$previousLocation = Get-Location
$exitCode = 1

function Enter-DistributedSetupLock {
    param([string]$Path)
    $stream = [IO.File]::Open($Path, [IO.FileMode]::OpenOrCreate,
                            [IO.FileAccess]::ReadWrite, [IO.FileShare]::ReadWrite)
    try {
        if ($stream.Length -eq 0) { $stream.WriteByte(49); $stream.Flush() }
        $stream.Lock(0, 1)
        $setupLocks.Add($stream)
    } catch {
        $stream.Dispose()
        throw 'Setup refused because another coordinator owns this checkout.'
    }
}

function Invoke-DistributedSetupCommand {
    param([string]$Label, [string]$Executable, [string[]]$Arguments)
    Write-Output $Label
    & $Executable @Arguments *>> $setupLog
    if ($LASTEXITCODE -ne 0) { throw 'A prerequisite command failed; private setup log retained.' }
}

try {
    Set-Location -LiteralPath $setupRoot
    . (Join-Path $PSScriptRoot 'distributed_env.ps1')
    New-DistributedDirectory (Join-Path $setupRoot '.verification\run') | Out-Null
    Add-Content -LiteralPath $setupLog -Value ('SETUP ' + [DateTime]::UtcNow.ToString('s') + 'Z')
    Enter-DistributedSetupLock (Join-Path $setupRoot '.verification\run\complete-run.lock')
    Enter-DistributedSetupLock (Join-Path $setupRoot '.verification\verifier.lock')
    $pythonExecutable = Resolve-DistributedPython -Python $Python
    $toolchainFile = Join-Path $setupRoot 'lean-toolchain'
    $manifestFile = Join-Path $setupRoot 'lake-manifest.json'
    $toolchainHash = (Get-FileHash -LiteralPath $toolchainFile -Algorithm SHA256).Hash
    $manifestHash = (Get-FileHash -LiteralPath $manifestFile -Algorithm SHA256).Hash
    $toolchain = (Get-Content -LiteralPath $toolchainFile -Raw).Trim()
    $elan = Join-Path $env:ELAN_HOME 'bin\elan.exe'
    $lake = Join-Path $env:ELAN_HOME 'bin\lake.exe'
    if (-not (Test-Path -LiteralPath $elan -PathType Leaf)) {
        if (-not $Install) { throw 'The scoped elan installation is missing; retry with -Install.' }
        $downloads = New-DistributedDirectory (Join-Path $distributedState 'downloads')
        $archive = Join-Path $downloads 'elan-v4.2.3-windows.zip'
        # Official GitHub release asset digest, verified at the expanded-assets URL:
        # https://github.com/leanprover/elan/releases/expanded_assets/v4.2.3
        $elanSha256 = 'be5e92a2dfdd8176099b2db0b810c27237c9054f1e5db1126f4f2a1134773b25'
        $elanUrl = 'https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-pc-windows-msvc.zip'
        if (-not (Test-Path -LiteralPath $archive -PathType Leaf)) {
            $download = Join-Path $downloads ('elan-' + [Guid]::NewGuid().ToString('N') + '.download')
            Write-Output 'Downloading the pinned public installer.'
            # No authorization headers or credentials are attached to redirects.
            Invoke-WebRequest -UseBasicParsing -Uri $elanUrl -OutFile $download *>> $setupLog
            if ((Get-FileHash -LiteralPath $download -Algorithm SHA256).Hash.ToLowerInvariant() -ne $elanSha256) {
                throw 'The pinned installer checksum does not match.'
            }
            Move-Item -LiteralPath $download -Destination $archive
        }
        if ((Get-FileHash -LiteralPath $archive -Algorithm SHA256).Hash.ToLowerInvariant() -ne $elanSha256) {
            throw 'The cached installer checksum does not match.'
        }
        $unpack = New-DistributedDirectory (Join-Path $env:TEMP ('elan-install-' + [Guid]::NewGuid().ToString('N')))
        Expand-Archive -LiteralPath $archive -DestinationPath $unpack *>> $setupLog
        $installer = Join-Path $unpack 'elan-init.exe'
        if (-not (Test-Path -LiteralPath $installer -PathType Leaf)) { throw 'Pinned installer is absent from its archive.' }
        Invoke-DistributedSetupCommand 'Installing the scoped toolchain manager.' $installer @('-y', '--no-modify-path', '--default-toolchain', 'none')
    }
    if ($Install) {
        Invoke-DistributedSetupCommand 'Restoring the pinned Lean toolchain.' $elan @('toolchain', 'install', $toolchain)
        Invoke-DistributedSetupCommand 'Restoring authenticated certificate sources.' $pythonExecutable @('-B', 'scripts/materialize_wand125.py')
        Invoke-DistributedSetupCommand 'Restoring the pinned dependency cache.' $lake @('exe', 'cache', 'get')
    }
    $installed = Join-Path $env:ELAN_HOME ('toolchains\' + $toolchain.Replace('/', '--').Replace(':', '---') + '\bin\lean.exe')
    if (-not (Test-Path -LiteralPath $installed -PathType Leaf) -or -not (Test-Path -LiteralPath $lake -PathType Leaf)) {
        throw 'Pinned Lean is unavailable; explicitly restore prerequisites with -Install.'
    }
    if (-not (Test-Path -LiteralPath (Join-Path $setupRoot '.lake\packages\mathlib') -PathType Container)) {
        throw 'Pinned dependencies are absent; explicitly restore prerequisites with -Install.'
    }
    if ((Get-FileHash -LiteralPath $toolchainFile -Algorithm SHA256).Hash -ne $toolchainHash -or
        (Get-FileHash -LiteralPath $manifestFile -Algorithm SHA256).Hash -ne $manifestHash) {
        throw 'Pinned configuration changed during setup; no setup acceptance is claimed.'
    }
    Write-Output 'SETUP_PREFLIGHT_PASS: pinned local prerequisites are present; worker validation remains mandatory.'
    $exitCode = 0
} catch {
    try { ($_ | Out-String) | Add-Content -LiteralPath $setupLog } catch { }
    Write-Output 'SETUP_REFUSED: inspect .verification/distributed/setup.log locally. No private details were printed.'
} finally {
    for ($index = $setupLocks.Count - 1; $index -ge 0; $index--) { $setupLocks[$index].Dispose() }
    Set-Location -LiteralPath $previousLocation.Path
}
exit $exitCode
