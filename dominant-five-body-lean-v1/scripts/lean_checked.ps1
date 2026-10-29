param(
    [Parameter(Mandatory=$true)][string]$SourceFile,
    [string]$OutputModule,
    [string]$LogFile
)
$ErrorActionPreference = 'Stop'
$taskRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Set-Location -LiteralPath $taskRoot
$env:LEAN_NUM_THREADS = '2'
New-Item -ItemType Directory -Path 'logs' -Force | Out-Null
$taskLockPath = Join-Path $taskRoot 'logs/lean-compiler.lock'
$taskLock = $null
while ($null -eq $taskLock) {
    try {
        $taskLock = [IO.File]::Open($taskLockPath,[IO.FileMode]::OpenOrCreate,
            [IO.FileAccess]::ReadWrite,[IO.FileShare]::None)
    } catch [IO.IOException] { Start-Sleep -Milliseconds 250 }
}
try {
    $taskArguments = @('env','lean','-DwarningAsError=true','-DautoImplicit=false')
    if ($OutputModule) { $taskArguments += @('-o',$OutputModule) }
    $taskArguments += $SourceFile
    if (-not $LogFile) {
        New-Item -ItemType Directory -Path 'logs/incremental' -Force | Out-Null
        $LogFile = 'logs/incremental/'+$SourceFile.Replace('\','.').Replace('/','.')+'.log'
    }
    $taskCommand = 'COMMAND: lake '+($taskArguments -join ' ')
    # Truncate before running: a successful silent Lean process still needs a
    # fresh receipt rather than leaving the previous failing log in place.
    Set-Content -LiteralPath $LogFile -Value $taskCommand -Encoding utf8
    Write-Output $taskCommand
    & lake @taskArguments 2>&1 | Tee-Object -FilePath $LogFile -Append
    $taskExit = $LASTEXITCODE
    Add-Content -LiteralPath $LogFile -Value ('LEAN_EXIT_CODE: '+$taskExit) -Encoding utf8
    if ((Get-Content -LiteralPath $LogFile -Raw) -match 'PANIC|sorryAx|declaration uses .sorry.') {
        $taskExit = 1
        Add-Content -LiteralPath $LogFile -Value 'Rejected compiler diagnostic despite process status.' -Encoding utf8
    }
    Add-Content -LiteralPath $LogFile -Value ('EXIT_CODE: '+$taskExit) -Encoding utf8
    Write-Output ('EXIT_CODE: '+$taskExit)
} finally { $taskLock.Dispose() }
exit $taskExit
