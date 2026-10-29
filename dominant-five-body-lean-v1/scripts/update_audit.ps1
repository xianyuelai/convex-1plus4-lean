param()
$ErrorActionPreference = 'Stop'
$taskRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Set-Location -LiteralPath $taskRoot

# Preserve line boundaries and handle nested Lean block comments.
function Remove-LeanComments([string]$Text) {
    $taskBuilder = [Text.StringBuilder]::new()
    $taskDepth = 0
    $taskLineComment = $false
    for ($taskIndex=0; $taskIndex -lt $Text.Length; $taskIndex++) {
        $taskChar = $Text[$taskIndex]
        $taskPair = if ($taskIndex+1 -lt $Text.Length) { $Text.Substring($taskIndex,2) } else { '' }
        if ($taskLineComment) {
            if ($taskChar -eq "`n") { $taskLineComment=$false; [void]$taskBuilder.Append($taskChar) }
            continue
        }
        if ($taskPair -eq '/-') { $taskDepth++; $taskIndex++; continue }
        if ($taskDepth -gt 0) {
            if ($taskPair -eq '-/') { $taskDepth--; $taskIndex++ }
            elseif ($taskChar -eq "`n") { [void]$taskBuilder.Append($taskChar) }
            continue
        }
        if ($taskPair -eq '--') { $taskLineComment=$true; $taskIndex++; continue }
        [void]$taskBuilder.Append($taskChar)
    }
    if ($taskDepth -ne 0) { throw 'Unbalanced Lean block comments.' }
    return $taskBuilder.ToString()
}

$taskFiles = @(Get-ChildItem -LiteralPath 'DominantFiveBody' -File -Recurse -Filter '*.lean' | Sort-Object FullName)
$taskOutput = [Collections.Generic.List[string]]::new()
$taskOutput.Add('/- Generated exact theorem inventory. Rebuild with scripts/update_audit.ps1. -/')
$taskDeclarations = [Collections.Generic.List[object]]::new()
foreach ($taskFile in $taskFiles) {
    $taskModule = $taskFile.FullName.Substring($taskRoot.Length+1).Replace('\','.').Replace('/','.').Replace('.lean','')
    $taskOutput.Add('import ' + $taskModule)
}
# The deliverable umbrella imports every formal mathematical module. The
# explicit build order and direct environment audit independently check this set.
@($taskOutput | Where-Object { $_.StartsWith('import ') }) |
    Set-Content -LiteralPath 'DominantFiveBody.lean' -Encoding utf8
$taskOutput.Add('')
foreach ($taskFile in $taskFiles) {
    $taskCode = Remove-LeanComments (Get-Content -LiteralPath $taskFile.FullName -Raw)
    $taskStack = [Collections.Generic.List[object]]::new()
    $taskLineNumber = 0
    foreach ($taskLine in $taskCode.Split("`n")) {
        $taskLineNumber++
        if ($taskLine -match '^\s*namespace\s+(\S+)') {
            $taskStack.Add(@{ kind='namespace'; name=$Matches[1] }); continue
        }
        if ($taskLine -match '^\s*(?:noncomputable\s+)?section(?:\s|$)') {
            $taskStack.Add(@{ kind='section'; name='' }); continue
        }
        if ($taskLine -match '^\s*end(?:\s+(\S+))?\s*$') {
            if ($taskStack.Count -eq 0) { throw ('Unexpected end in ' + $taskFile.Name) }
            $taskStack.RemoveAt($taskStack.Count-1); continue
        }
        if ($taskLine -match '^\s*(?:@\[[^\]]+\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+(\S+)') {
            $taskName = $Matches[1]
            $taskNamespace = (@($taskStack | Where-Object { $_.kind -eq 'namespace' } | ForEach-Object { $_.name }) -join '.')
            $taskQualifiedName = if ($taskNamespace) { $taskNamespace+'.'+$taskName } else { $taskName }
            $taskOutput.Add('#print axioms ' + $taskQualifiedName)
            $taskDeclarations.Add(@{ name=$taskQualifiedName; file=$taskFile.FullName.Substring($taskRoot.Length+1).Replace('\','/'); line=$taskLineNumber })
        } elseif ($taskLine -match '^\s*(?:@\[[^\]]+\]\s*)?private\s+(?:theorem|lemma)\s') {
            throw ('Private declaration requires an environment-name audit: ' + $taskFile.Name)
        }
    }
}
if ($taskDeclarations.Count -eq 0) { throw 'Empty theorem inventory.' }
$taskOutput | Set-Content -LiteralPath 'Audit/AllTheorems.lean' -Encoding utf8
$taskEnvironment = @($taskOutput | Where-Object { $_.StartsWith('import ') })
$taskEnvironment += Get-Content -LiteralPath 'scripts/environment_audit_body.lean.txt'
$taskEnvironment | Set-Content -LiteralPath 'Audit/Environment.lean' -Encoding utf8
@{ inventory_complete=$true; declarations=$taskDeclarations.ToArray() } | ConvertTo-Json -Depth 6 |
    Set-Content -LiteralPath 'logs/THEOREM_INVENTORY.json' -Encoding utf8
Write-Output ('Inventoried ' + $taskDeclarations.Count + ' declarations in ' + $taskFiles.Count + ' physical modules.')
