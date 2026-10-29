param([switch]$Clean, [switch]$ResumeCleanMath)
if ($Clean -and $ResumeCleanMath) { throw 'Clean and ResumeCleanMath are mutually exclusive.' }
$ErrorActionPreference = 'Stop'
$taskRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Set-Location -LiteralPath $taskRoot
$env:LEAN_NUM_THREADS = '2'
if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
    $taskGit = Join-Path $env:USERPROFILE '.cache/codex-runtimes/codex-primary-runtime/dependencies/native/git/cmd'
    if (Test-Path -LiteralPath (Join-Path $taskGit 'git.exe')) { $env:PATH = $taskGit + ';' + $env:PATH }
}
New-Item -ItemType Directory -Path 'logs' -Force | Out-Null
$taskChecks = [Collections.Generic.List[object]]::new()
$taskRecord = [ordered]@{
    created_at = [DateTimeOffset]::Now.ToString('o')
    paper_verified = $false
    acceptance_target = 'PaperAcceptance'
    commands_executed = @()
    failure = $null
}
# Invalidate first, even if the release metadata itself is missing or invalid.
$taskRecord | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'logs/PAPER_ACCEPTANCE.json' -Encoding utf8
$taskVersion = Get-Content -LiteralPath 'VERSION.json' -Raw | ConvertFrom-Json
if ($taskVersion.version -cne 'v1') { throw 'Expected the frozen v1 release identity.' }
$taskRecord['version'] = $taskVersion.version
$taskRecord['source_identity'] = $taskVersion.source_identity
# Invalidate an older success before any subprocess can fail or be interrupted.
$taskRecord | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'logs/PAPER_ACCEPTANCE.json' -Encoding utf8
function Invoke-PaperCheck {
    param([string]$Program, [string[]]$Arguments, [string]$LogName, [switch]$Compiler)
    $taskStarted = [DateTimeOffset]::Now
    $taskLock = $null
    if ($Compiler) {
        while ($null -eq $taskLock) {
            try { $taskLock = [IO.File]::Open((Join-Path $taskRoot 'logs/lean-compiler.lock'),
                [IO.FileMode]::OpenOrCreate,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None) }
            catch [IO.IOException] { Start-Sleep -Milliseconds 250 }
        }
    }
    try {
        & $Program @Arguments 2>&1 | Out-File -LiteralPath $LogName -Encoding utf8
        $taskExit = $LASTEXITCODE
    } finally { if ($null -ne $taskLock) { $taskLock.Dispose() } }
    $taskChecks.Add([ordered]@{ command=$Program+' '+($Arguments -join ' '); exit_code=$taskExit;
        log=$LogName; started_at=$taskStarted.ToString('o');
        elapsed_seconds=([DateTimeOffset]::Now-$taskStarted).TotalSeconds })
    if ($taskExit -ne 0) { Get-Content -LiteralPath $LogName -Tail 25; throw ('Failed: '+$Program+' '+($Arguments -join ' ')) }
    if ((Get-Content -LiteralPath $LogName -Raw) -match 'PANIC|sorryAx|declaration uses .sorry.') {
        throw ('Rejected compiler diagnostic in '+$LogName)
    }
    Write-Output ('PASS: '+$Program+' '+($Arguments -join ' '))
}
function Get-PaperHashes {
    $taskPaths = @('DominantFiveBody','Audit','PaperAcceptance','scripts','source','docs','paper-reading')
    $taskFiles = @(foreach ($taskDir in $taskPaths) { Get-ChildItem -LiteralPath $taskDir -File -Recurse }) +
        @(Get-ChildItem -LiteralPath $taskRoot -File | Where-Object { $_.Extension -eq '.lean' -or $_.Name -in @('lakefile.toml','lake-manifest.json','lean-toolchain','README.md','FINAL_REPORT.md','PROOF_PACKAGE.md','VERSION.json','.gitignore','.gitattributes') }) +
        @(Get-Item -LiteralPath 'logs/SOURCE_BINDING.json','logs/history/pre-v1/FULL_ASSERTIONS.json')
    $taskHashes = [ordered]@{}
    foreach ($taskFile in $taskFiles | Sort-Object FullName) {
        if ($taskFile.Extension -in @('.pyc','.log')) { continue }
        $taskRel = $taskFile.FullName.Substring($taskRoot.Length+1).Replace('\','/')
        $taskHashes[$taskRel] = (Get-FileHash -LiteralPath $taskFile.FullName -Algorithm SHA256).Hash
    }
    return $taskHashes
}
function Assert-AxiomOutput {
    param([string]$LogName, [string[]]$ExpectedNames)
    $taskText = Get-Content -LiteralPath $LogName -Raw
    $taskMatches = [regex]::Matches($taskText, "'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    if ($taskMatches.Count -ne $ExpectedNames.Count) { throw ('Incomplete axiom audit: '+$LogName) }
    $taskSeen = [Collections.Generic.HashSet[string]]::new()
    foreach ($taskMatch in $taskMatches) {
        $taskName = $taskMatch.Groups[1].Value
        if ($taskName -notin $ExpectedNames -or -not $taskSeen.Add($taskName)) { throw ('Unexpected or duplicate axiom target: '+$taskName) }
        foreach ($taskAxiom in $taskMatch.Groups[2].Value.Split(',')) {
            if ($taskAxiom.Trim() -and $taskAxiom.Trim() -notin @('Classical.choice','propext','Quot.sound')) { throw ('Disallowed axiom: '+$taskAxiom.Trim()) }
        }
    }
}
function Assert-CoverageBinding {
    param($Expected)
    if ((Get-FileHash -LiteralPath 'docs/FULL_ASSERTIONS.json' -Algorithm SHA256).Hash -cne $Expected.ledger_sha256 -or
        (Get-FileHash -LiteralPath 'docs/DEFINITION_BINDINGS.json' -Algorithm SHA256).Hash -cne $Expected.definition_bindings_sha256 -or
        (Get-FileHash -LiteralPath 'PaperAcceptance/Coverage.lean' -Algorithm SHA256).Hash -cne $Expected.coverage_lean_sha256) {
        throw 'The coverage target does not bind the current ledger and definition bytes.'
    }
}
try {
    # This is deliberately first. No open/partial/conditional row can pass.
    Invoke-PaperCheck 'python' @('-I','-X','utf8','scripts/paper_coverage.py','--generate') 'logs/paper-coverage-metadata.log'
    Invoke-PaperCheck 'python' @('-I','-X','utf8','scripts/v1_source_negative_controls.py') 'logs/v1-source-negative-controls.log'
    Invoke-PaperCheck 'pwsh' @('-NoProfile','-File','scripts/update_audit.ps1') 'logs/paper-inventory.log'
    $taskBefore = Get-PaperHashes
    $taskExpected = Get-Content -LiteralPath 'logs/PAPER_COVERAGE_EXPECTED.json' -Raw | ConvertFrom-Json
    Assert-CoverageBinding $taskExpected
    if (-not $taskExpected.whole_paper_closed -or $taskExpected.unclosed_assertions.Count -ne 0) { throw 'Whole-paper ledger still has open obligations.' }
    $taskVerifyArgs = @('-NoProfile','-File','scripts/verify.ps1')
    if ($Clean) { $taskVerifyArgs += '-Clean' }
    if ($ResumeCleanMath) { $taskVerifyArgs += '-ResumeCleanMath' }
    Invoke-PaperCheck 'pwsh' $taskVerifyArgs 'logs/paper-development-verification.log'
    $taskDevelopment = Get-Content -LiteralPath 'logs/VERIFICATION.json' -Raw | ConvertFrom-Json
    if (-not $taskDevelopment.verification_complete -or -not $taskDevelopment.main_uniform_proved -or
        -not $taskDevelopment.all_declared_theorems_axiom_audited) { throw 'Development verification lacks required checks.' }
    Invoke-PaperCheck 'lake' @('build','PaperAcceptance') 'logs/paper-acceptance-build.log' -Compiler
    Invoke-PaperCheck 'lake' @('env','lean','-DwarningAsError=true','-DautoImplicit=false','PaperAcceptance/Main.lean') 'logs/paper-main.log' -Compiler
    Assert-AxiomOutput 'logs/paper-main.log' @('DominantFiveBody.main_uniform')
    Invoke-PaperCheck 'lake' @('env','lean','-DwarningAsError=true','-DautoImplicit=false','PaperAcceptance/Coverage.lean') 'logs/paper-coverage.log' -Compiler
    Assert-AxiomOutput 'logs/paper-coverage.log' @($taskExpected.axiom_names)
    $taskCheckerPath = $taskDevelopment.checker.path
    if (-not $taskCheckerPath -or -not (Test-Path -LiteralPath $taskCheckerPath -PathType Leaf) -or
        (Get-FileHash -LiteralPath $taskCheckerPath -Algorithm SHA256).Hash -cne $taskDevelopment.checker.sha256) {
        throw 'The distribution checker changed after development verification.'
    }
    Invoke-PaperCheck 'lake' @('env',$taskCheckerPath,'--fresh','PaperAcceptance') 'logs/paper-kernel.log' -Compiler
    $taskAfter = Get-PaperHashes
    Assert-CoverageBinding $taskExpected
    if (($taskBefore | ConvertTo-Json -Compress) -cne ($taskAfter | ConvertTo-Json -Compress)) { throw 'Source, ledger, definitions or verification scripts changed during acceptance.' }
    $taskRecord.paper_verified = $true
    $taskRecord['coverage'] = $taskExpected
    $taskRecord['development_receipt_sha256'] = (Get-FileHash -LiteralPath 'logs/VERIFICATION.json' -Algorithm SHA256).Hash
    $taskRecord['source_and_code_sha256'] = $taskAfter
    $taskRecord['allowed_axioms'] = @('Classical.choice','propext','Quot.sound')
    $taskRecord.commands_executed = $taskChecks.ToArray()
    $taskRecord | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'logs/PAPER_ACCEPTANCE.json' -Encoding utf8
    'WHOLE PAPER VERIFIED'
    exit 0
} catch {
    $taskRecord.failure = $_.Exception.Message
    $taskRecord.commands_executed = $taskChecks.ToArray()
    $taskRecord | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'logs/PAPER_ACCEPTANCE.json' -Encoding utf8
    Write-Output ('WHOLE PAPER ACCEPTANCE FAILED: '+$taskRecord.failure)
    exit 1
}
