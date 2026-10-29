param([switch]$Clean, [switch]$ResumeCleanMath)
if ($Clean -and $ResumeCleanMath) { throw 'Clean and ResumeCleanMath are mutually exclusive.' }

$ErrorActionPreference = 'Stop'
$taskRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Set-Location -LiteralPath $taskRoot
$env:LEAN_NUM_THREADS = '2'

if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
    $taskBundledGit = Join-Path $env:USERPROFILE '.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd'
    if (Test-Path -LiteralPath (Join-Path $taskBundledGit 'git.exe')) {
        $env:PATH = $taskBundledGit + ';' + $env:PATH
    } else { throw 'Git is required to use the locked Lake manifest.' }
}

New-Item -ItemType Directory -Path (Join-Path $taskRoot 'logs') -Force | Out-Null
$taskChecks = [System.Collections.Generic.List[object]]::new()
@{ created_at=[DateTimeOffset]::Now.ToString('o'); main_uniform_proved=$false;
    all_declared_theorems_axiom_audited=$false; verification_complete=$false;
    status='RUNNING_OR_INTERRUPTED' } | ConvertTo-Json |
    Set-Content -LiteralPath 'logs/VERIFICATION.json' -Encoding utf8

function Invoke-Logged {
    param([string]$Program, [string[]]$Arguments, [string]$LogName)
    $taskLogPath = Join-Path $taskRoot ('logs\' + $LogName)
    $taskStarted = [DateTimeOffset]::Now
    & $Program @Arguments 2>&1 | Out-File -LiteralPath $taskLogPath -Encoding utf8
    $taskExit = $LASTEXITCODE
    $taskChecks.Add([ordered]@{
        command = $Program + ' ' + ($Arguments -join ' ')
        exit_code = $taskExit
        log = 'logs/' + $LogName
        started_at = $taskStarted.ToString('o')
        elapsed_seconds = ([DateTimeOffset]::Now - $taskStarted).TotalSeconds
    })
    if ($taskExit -ne 0) {
        Get-Content -LiteralPath $taskLogPath -Tail 40
        throw "Command failed (exit $taskExit): $Program $($Arguments -join ' ')"
    }
    if ((Get-Content -LiteralPath $taskLogPath -Raw) -match 'PANIC|sorryAx|declaration uses .sorry.') {
        throw ('Rejected compiler diagnostic in '+$taskLogPath)
    }
    Write-Output "PASS: $Program $($Arguments -join ' ')"
}

# Serialize the entire clean/build/audit/replay sequence against proof workers.
$taskCompilerLock = $null
while ($null -eq $taskCompilerLock) {
    try { $taskCompilerLock = [IO.File]::Open((Join-Path $taskRoot 'logs/lean-compiler.lock'),
        [IO.FileMode]::OpenOrCreate,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None) }
    catch [IO.IOException] { Start-Sleep -Milliseconds 250 }
}
try {
if ($Clean) {
    # Remove only this project's build directory. Never traverse the shared
    # dependency-cache junction at .lake/packages.
    $taskBuildPath = [System.IO.Path]::GetFullPath((Join-Path $taskRoot '.lake\build'))
    $taskExpected = $taskRoot.TrimEnd('\') + '\.lake\build'
    if ($taskBuildPath -ne $taskExpected) { throw 'Unexpected clean target.' }
    if (Test-Path -LiteralPath $taskBuildPath) {
        $taskBuildItem = Get-Item -LiteralPath $taskBuildPath -Force
        if ($taskBuildItem.LinkType) { throw 'Refusing to clean a linked build directory.' }
        if ((Resolve-Path -LiteralPath $taskBuildPath).Path -ne $taskExpected) {
            throw 'Resolved clean target escaped the project.'
        }
        Remove-Item -LiteralPath $taskBuildPath -Recurse -Force
    }
}

Invoke-Logged 'lake' @('env', 'lean', '--version') 'toolchain.log'
if ((Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim() -cne 'leanprover/lean4:v4.33.1' -or
    (Get-Content -LiteralPath 'logs/toolchain.log' -Raw) -notmatch 'Lean \(version 4\.33\.1(?:,|\s)') {
    throw 'The active Lean executable or locked toolchain differs from Lean 4.33.1.'
}
Invoke-Logged 'lake' @('env', 'lean', '--print-prefix') 'toolchain-prefix.log'
Invoke-Logged 'lake' @('env', 'where.exe', 'leanchecker') 'checker-path.log'
$taskLeanPrefix = (Get-Content -LiteralPath 'logs/toolchain-prefix.log' -Raw).Trim()
$taskExpectedChecker = [IO.Path]::GetFullPath((Join-Path $taskLeanPrefix 'bin/leanchecker.exe'))
$taskCheckerCandidates = @(Get-Content -LiteralPath 'logs/checker-path.log' |
    ForEach-Object { [IO.Path]::GetFullPath($_.Trim()) })
if (-not ($taskCheckerCandidates -icontains $taskExpectedChecker) -or
    -not (Test-Path -LiteralPath $taskExpectedChecker -PathType Leaf)) {
    throw 'The active locked Lean distribution checker was not found.'
}
# PATH may list the elan shim first. Invoke the verified distribution binary
# explicitly, under lake env, instead of treating the shim as that binary.
$taskCheckerPath = $taskExpectedChecker
$taskCheckerHash = (Get-FileHash -LiteralPath $taskCheckerPath -Algorithm SHA256).Hash
Invoke-Logged 'git' @('-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD') 'mathlib-revision.log'
$taskRev = (Get-Content -LiteralPath 'logs/mathlib-revision.log' -Raw).Trim()
if ($taskRev -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Unexpected mathlib revision.' }
$taskDependencyRevisions = [ordered]@{}
$taskManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
foreach ($taskPackage in $taskManifest.packages) {
    if ($taskPackage.type -ne 'git' -or -not $taskPackage.rev) {
        throw ('Unpinned dependency: '+$taskPackage.name)
    }
    $taskPackageLog = 'dependency-'+$taskPackage.name+'.log'
    Invoke-Logged 'git' @('-C',('.lake/packages/'+$taskPackage.name),'rev-parse','HEAD') $taskPackageLog
    $taskPackageRevision = (Get-Content -LiteralPath ('logs/'+$taskPackageLog) -Raw).Trim()
    if ($taskPackageRevision -cne $taskPackage.rev) { throw ('Dependency differs from lock: '+$taskPackage.name) }
    $taskDependencyRevisions[$taskPackage.name] = $taskPackageRevision
}
& pwsh -NoProfile -File scripts/update_audit.ps1
if ($LASTEXITCODE -ne 0) { throw 'Cannot create the exhaustive theorem inventory.' }
$taskModules = @(Get-ChildItem -LiteralPath 'DominantFiveBody' -File -Recurse -Filter '*.lean' |
    Sort-Object FullName | ForEach-Object {
        $_.FullName.Substring($taskRoot.Length+1).Replace('\','.').Replace('/','.').Replace('.lean','')
    })
# Every mathematical module is explicitly built, including any loose module
# accidentally omitted from the umbrella imports.
Invoke-Logged 'python' @('scripts/module_build_order.py') 'module-build-order.log'
$taskBuildOrder = @(Get-Content -LiteralPath 'logs/MODULE_BUILD_ORDER.json' -Raw | ConvertFrom-Json)
if ((($taskBuildOrder | Sort-Object) -join ',') -cne (($taskModules | Sort-Object) -join ',')) {
    throw 'Incomplete mathematical build order.'
}
New-Item -ItemType Directory -Path 'logs/modules' -Force | Out-Null
$taskPriorClean = $null
if ($ResumeCleanMath) {
    # Only the post-build audit generator may have changed. Reuse a recorded
    # completed clean mathematical build iff its entire source, olean, lockfile
    # and ordered successful command log still match byte for byte.
    $taskPriorClean = Get-Content -LiteralPath 'logs/CLEAN_MATH_BUILD.json' -Raw | ConvertFrom-Json
    if (($taskPriorClean.clean_mathematical_modules -join ',') -cne ($taskBuildOrder -join ',')) {
        throw 'The prior clean build covers a different mathematical module set.'
    }
    $taskExpectedSources = @($taskModules | ForEach-Object { $_.Replace('.','/')+'.lean' } | Sort-Object)
    $taskExpectedArtifacts = @($taskModules | ForEach-Object { '.lake/build/lib/lean/'+$_.Replace('.','/')+'.olean' } | Sort-Object)
    if ((@($taskPriorClean.source_sha256.PSObject.Properties.Name | Sort-Object) -join ',') -cne ($taskExpectedSources -join ',') -or
        (@($taskPriorClean.artifact_sha256.PSObject.Properties.Name | Sort-Object) -join ',') -cne ($taskExpectedArtifacts -join ',') -or
        (@($taskPriorClean.locked_configuration_sha256.PSObject.Properties.Name | Sort-Object) -join ',') -cne 'lake-manifest.json,lakefile.toml,lean-toolchain') {
        throw 'Incomplete clean-build source or artifact binding.'
    }
    foreach ($taskMap in @($taskPriorClean.source_sha256,$taskPriorClean.artifact_sha256,$taskPriorClean.locked_configuration_sha256)) {
        foreach ($taskEntry in $taskMap.PSObject.Properties) {
            if ((Get-FileHash -LiteralPath $taskEntry.Name -Algorithm SHA256).Hash -cne $taskEntry.Value) {
                throw ('Prior clean build no longer matches: '+$taskEntry.Name)
            }
        }
    }
    if ((Get-FileHash -LiteralPath $taskPriorClean.raw_command_record -Algorithm SHA256).Hash -cne $taskPriorClean.raw_command_record_sha256) {
        throw 'Prior clean-build command record changed.'
    }
    $taskPriorPasses = @(Select-String -LiteralPath $taskPriorClean.raw_command_record -Pattern '^PASS: lake build (DominantFiveBody\..+)$' |
        ForEach-Object { $_.Matches[0].Groups[1].Value })
    if (($taskPriorPasses -join ',') -cne ($taskBuildOrder -join ',')) { throw 'Prior clean build has missing successful module commands.' }
    Write-Output ('Validated prior clean mathematical build: '+$taskModules.Count+' modules; all source and olean hashes match.')
} else {
    foreach ($taskModule in $taskBuildOrder) {
        Invoke-Logged 'lake' @('build', $taskModule) ('modules/'+$taskModule+'.log')
    }
}
Invoke-Logged 'lake' @('build', 'DominantFiveBody', 'Audit') 'clean-build.log'
Invoke-Logged 'lake' @('env', 'lean', '-DwarningAsError=true', 'Audit/Main.lean') 'specification-audit.log'
Invoke-Logged 'lake' @('env', 'lean', '-DwarningAsError=true', 'Audit/AllTheorems.lean') 'all-axioms.log'
if (Test-Path -LiteralPath 'logs/ENVIRONMENT_AUDIT.json') {
    Remove-Item -LiteralPath 'logs/ENVIRONMENT_AUDIT.json' -Force
}
Invoke-Logged 'lake' @('env', 'lean', '-DwarningAsError=true', '-DautoImplicit=false', 'Audit/Environment.lean') 'environment-audit.log'
$taskEnvironmentAudit = Get-Content -LiteralPath 'logs/ENVIRONMENT_AUDIT.json' -Raw | ConvertFrom-Json
if (-not $taskEnvironmentAudit.passed) { throw 'Direct proof-body environment audit failed.' }
if ((($taskModules | Sort-Object) -join ',') -cne (($taskEnvironmentAudit.modules | Sort-Object) -join ',')) {
    throw 'Direct environment audit did not cover exactly all mathematical modules.'
}
Invoke-Logged 'lake' @('env', $taskCheckerPath, '--fresh', 'Audit') 'fresh-kernel.log'

$taskAxiomText = Get-Content -LiteralPath 'logs/all-axioms.log' -Raw
$taskExpectedAuditCount = @(Select-String -LiteralPath 'Audit/AllTheorems.lean' -Pattern '^#print axioms ').Count
$taskObservedAuditCount = [regex]::Matches($taskAxiomText, 'depends on axioms:|does not depend on any axioms').Count
if ($taskObservedAuditCount -ne $taskExpectedAuditCount) { throw 'Incomplete theorem axiom audit output.' }
$taskAllowed = @('propext', 'Classical.choice', 'Quot.sound')
$taskUsed = [System.Collections.Generic.HashSet[string]]::new()
foreach ($taskMatch in [regex]::Matches($taskAxiomText, 'depends on axioms:\s*\[([^\]]*)\]')) {
    foreach ($taskName in $taskMatch.Groups[1].Value.Split(',')) {
        $taskName = $taskName.Trim()
        if ($taskName) {
            [void]$taskUsed.Add($taskName)
            if ($taskName -notin $taskAllowed) { throw "Disallowed axiom dependency: $taskName" }
        }
    }
}

$taskFiles = @(Get-ChildItem -LiteralPath $taskRoot -File -Filter '*.lean') +
    @(Get-ChildItem -LiteralPath (Join-Path $taskRoot 'DominantFiveBody') -File -Filter '*.lean') +
    @(Get-ChildItem -LiteralPath (Join-Path $taskRoot 'Audit') -File -Filter '*.lean')
Invoke-Logged 'python' @('scripts/scan_proof_sources.py') 'source-proof-scan.log'

$taskHashes = [ordered]@{}
$taskBindingFiles = $taskFiles +
    @(Get-ChildItem -LiteralPath (Join-Path $taskRoot 'source') -File) +
    @(Get-Item -LiteralPath 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
foreach ($taskFile in $taskBindingFiles | Sort-Object FullName) {
    $taskRelative = $taskFile.FullName.Substring($taskRoot.Length + 1).Replace('\', '/')
    $taskHashes[$taskRelative] = (Get-FileHash -LiteralPath $taskFile.FullName -Algorithm SHA256).Hash
}
$taskReceipt = [ordered]@{
    created_at = [DateTimeOffset]::Now.ToString('o')
    verification_complete = $true
    verification_scope = 'All project mathematical modules and unconditional Theorem 1.1. Whole-paper assertion coverage is checked separately by verify_paper.ps1.'
    main_uniform_proved = $true
    main_theorem_specification = 'DominantFiveBody.MainUniformStatement'
    unconditional_main_theorem = 'DominantFiveBody.main_uniform'
    clean_project_build = [bool]$Clean
    prior_clean_mathematical_build = if ($ResumeCleanMath) { @{
        receipt='logs/CLEAN_MATH_BUILD.json';
        sha256=(Get-FileHash -LiteralPath 'logs/CLEAN_MATH_BUILD.json' -Algorithm SHA256).Hash;
        mathematical_modules=$taskModules.Count;
        source_and_artifact_bytes_revalidated=$true } } else { $null }
    allowed_axioms_observed = @($taskUsed | Sort-Object)
    all_declared_theorems_axiom_audited = $true
    direct_environment_audit = $taskEnvironmentAudit
    axiom_audit_count = $taskObservedAuditCount
    dependency_cache_reused = $true
    dependency_revisions = $taskDependencyRevisions
    checker = @{ path=$taskCheckerPath; sha256=$taskCheckerHash;
        distribution='leanprover/lean4:v4.33.1'; method='Fresh replay with the same Lean kernel' }
    checks = $taskChecks.ToArray()
    source_and_code_sha256 = $taskHashes
}
$taskReceipt | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath 'logs/VERIFICATION.json' -Encoding utf8
Write-Output 'All project declarations and unconditional Theorem 1.1 verified; whole-paper coverage requires verify_paper.ps1.'

} finally { $taskCompilerLock.Dispose() }
