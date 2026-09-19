param(
  [string]$PackageRoot = 'E:\Lean 4\Sendov_conjecture_explicit_n0\.lake\packages',
  [switch]$Fresh,
  [ValidateRange(1,8)][int]$ModuleBatchSize = 4
)
$ErrorActionPreference = 'Stop'
$leanVersion = 'v4.34.0-rc1'
$lakeBin = Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---$leanVersion\bin\lake.exe"
if (!(Test-Path -LiteralPath $lakeBin)) { throw "Missing Lean toolchain $leanVersion" }
$librarySources = @(Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'ModifiedCartan') -Filter '*.lean' -File -Recurse)
$rootSources = @(Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' -File)
$sources = $librarySources + $rootSources
$names = @()
foreach ($source in $sources) {
  $body = [IO.File]::ReadAllText($source.FullName)
  if ($body -match '(?m)^\s*(axiom|opaque)\s|\b(sorry|admit|unsafe|native_decide)\b') {
    throw "Unverified declaration or placeholder: $($source.Name)"
  }
  foreach ($match in [regex]::Matches($body, '(?m)^(?:theorem|lemma)\s+([\w.]+)')) {
    $names += 'ModifiedCartan.' + $match.Groups[1].Value
  }
}
$auditText = [IO.File]::ReadAllText((Join-Path $PSScriptRoot 'Audit.lean'))
$auditNames = @([regex]::Matches($auditText, '(?m)^#print axioms (\S+)') | ForEach-Object { $_.Groups[1].Value })
if (Compare-Object ($names | Sort-Object) ($auditNames | Sort-Object)) {
  throw 'Audit.lean must list every theorem in the local source files.'
}
$coveragePath = Join-Path $PSScriptRoot 'verification/manuscript-coverage.json'
$coverage = Get-Content -LiteralPath $coveragePath -Raw | ConvertFrom-Json
if ($coverage.review.status -ne 'complete') { throw 'Manuscript correspondence review is incomplete.' }
$paperPath = Join-Path $PSScriptRoot $coverage.manuscript.file
$paperHash = (Get-FileHash -LiteralPath $paperPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($paperHash -ne $coverage.manuscript.sha256) { throw 'Manuscript has changed since correspondence review.' }
$paperText = [IO.File]::ReadAllText($paperPath)
$paperLabels = @()
foreach ($block in [regex]::Matches($paperText, '(?s)\\begin\{(thm|lem|prop|cor)\}(.*?)\\end\{\1\}')) {
  $label = [regex]::Match($block.Groups[2].Value, '\\label\{([^}]+)\}')
  if (!$label.Success) { throw 'A principal manuscript statement lacks a coverage label.' }
  $paperLabels += $label.Groups[1].Value
}
if ($paperLabels.Count -ne 19 -or (Compare-Object ($paperLabels | Sort-Object) ($coverage.principal_results.label | Sort-Object))) {
  throw 'Principal manuscript label coverage mismatch.'
}
$coveredProofs = @()
foreach ($entry in @($coverage.principal_results) + @($coverage.supplemental_results)) {
  if ($entry.status -ne 'proof_complete' -or $entry.proofs.Count -eq 0) { throw 'An entry has no completed proof.' }
  foreach ($proof in $entry.proofs) {
    if ($names -notcontains $proof.name) { throw "Proof absent from theorem audit: $($proof.name)" }
    $sourceText = [IO.File]::ReadAllText((Join-Path $PSScriptRoot $proof.file))
    $shortName = $proof.name -replace '^ModifiedCartan\.', ''
    if ($sourceText -notmatch ('(?m)^(?:theorem|lemma)\s+' + [regex]::Escape($shortName) + '(?=\s|\{)')) {
      throw "Incorrect proof source: $($proof.name)"
    }
    $coveredProofs += $proof.name
  }
}
if ($coverage.definitions.Count -ne 1 -or $coverage.definitions[0].label -ne 'def:cclass' -or $coverage.definitions[0].status -ne 'reviewed') {
  throw 'C-class definition review is missing.'
}
foreach ($decl in $coverage.definitions[0].declarations) {
  $sourceText = [IO.File]::ReadAllText((Join-Path $PSScriptRoot $decl.file))
  $shortName = $decl.name -replace '^ModifiedCartan\.', ''
  if ($sourceText -notmatch ('(?m)^(?:def|structure)\s+' + [regex]::Escape($shortName) + '(?=\s|\{)')) {
    throw "Missing reviewed definition: $($decl.name)"
  }
}
$coveredProofs = @($coveredProofs | Sort-Object -Unique)
$checkText = [IO.File]::ReadAllText((Join-Path $PSScriptRoot 'ManuscriptCheck.lean'))
$checkNames = @([regex]::Matches($checkText, '(?m)^#check (\S+)') | ForEach-Object { $_.Groups[1].Value })
if (Compare-Object $coveredProofs ($checkNames | Sort-Object -Unique)) { throw 'Manuscript entry-point checks are incomplete.' }
$suffix = if ($Fresh) { [guid]::NewGuid().ToString('N') } else { 'verified' }
$stage = Join-Path $env:TEMP ('ModifiedCartan-' + $suffix)
[IO.Directory]::CreateDirectory($stage) | Out-Null
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
$overrides = @()
foreach ($package in $manifest.packages) {
  $packagePath = Join-Path $PackageRoot $package.name
  $rev = (& git -C $packagePath rev-parse HEAD | Out-String).Trim()
  if ($LASTEXITCODE -ne 0 -or $rev -ne $package.rev) { throw "Dependency revision mismatch: $($package.name)" }
  & git -C $packagePath diff --quiet HEAD --
  if ($LASTEXITCODE -ne 0) { throw "Dependency has tracked modifications: $($package.name)" }
  $overrides += [ordered]@{
    name = $package.name; scope = $package.scope; type = 'path'; dir = $packagePath
    inherited = $package.inherited; configFile = $package.configFile; manifestFile = $package.manifestFile
  }
}
$overrideFile = Join-Path $stage 'local-packages.json'
[IO.File]::WriteAllText($overrideFile, (ConvertTo-Json -InputObject @{
  schemaVersion = '1.2.0'; packages = $overrides
} -Depth 10))
$inputs = $sources + @(Get-ChildItem -LiteralPath $PSScriptRoot -File | Where-Object {
  $_.Name -in @('lakefile.toml','lean-toolchain','lake-manifest.json','paper.tex','verify.ps1')
}) + @(Get-Item -LiteralPath $coveragePath)
$hashes = @()
foreach ($file in $inputs) {
  $rel = [IO.Path]::GetRelativePath($PSScriptRoot, $file.FullName)
  $dest = Join-Path $stage $rel
  [IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($dest)) | Out-Null
  [IO.File]::Copy($file.FullName, $dest, $true)
  $hash = (Get-FileHash -LiteralPath $file.FullName -Algorithm SHA256).Hash
  if ((Get-FileHash -LiteralPath $dest -Algorithm SHA256).Hash -ne $hash) { throw "Copy mismatch: $rel" }
  $hashes += [ordered]@{ file = $rel; sha256 = $hash }
}
[IO.File]::WriteAllText((Join-Path $stage 'source-hashes.json'), (ConvertTo-Json -InputObject $hashes -Depth 5))
$priorLeanPath = $env:LEAN_PATH
$priorLeanThreads = $env:LEAN_NUM_THREADS
try {
  $env:LEAN_PATH = ''
  Remove-Item Env:LEAN_NUM_THREADS -ErrorAction SilentlyContinue
  Push-Location $stage
  Write-Output "Verification directory: $stage"
  # Bound simultaneous local compiler processes on this Windows installation.
  # Every batch contains only modules whose local imports are already built.
  $pending = @{}
  foreach ($file in $librarySources + @(Get-Item -LiteralPath (Join-Path $PSScriptRoot 'ModifiedCartan.lean'))) {
    $moduleName = ([IO.Path]::GetRelativePath($PSScriptRoot, $file.FullName) -replace '\.lean$', '') -replace '[\\/]', '.'
    $body = [IO.File]::ReadAllText($file.FullName)
    $pending[$moduleName] = @([regex]::Matches($body, '(?m)^import\s+(ModifiedCartan(?:\.[\w]+)?)\s*$') | ForEach-Object { $_.Groups[1].Value })
  }
  $built = [Collections.Generic.HashSet[string]]::new()
  $buildLog = Join-Path $stage 'build.log'
  [IO.File]::WriteAllText($buildLog, '')
  while ($pending.Count -gt 0) {
    $ready = @($pending.Keys | Where-Object {
      @($pending[$_] | Where-Object { !$built.Contains($_) }).Count -eq 0
    } | Sort-Object)
    if ($ready.Count -eq 0) { throw 'Local import graph is cyclic or incomplete.' }
    $batch = @($ready | Select-Object -First $ModuleBatchSize)
    Write-Output ("Building batch: " + ($batch -join ', ')) | Tee-Object -FilePath $buildLog -Append
    & $lakeBin --packages $overrideFile --log-level=error build @batch 2>&1 | Tee-Object -FilePath $buildLog -Append
    if ($LASTEXITCODE -ne 0) { throw 'Lake module batch failed.' }
    foreach ($moduleName in $batch) { [void]$built.Add($moduleName); $pending.Remove($moduleName) }
  }
  & $lakeBin --packages $overrideFile build 2>&1 | Tee-Object -FilePath $buildLog -Append
  if ($LASTEXITCODE -ne 0) { throw 'Lake build failed.' }
  & $lakeBin --packages $overrideFile env lean ManuscriptCheck.lean 2>&1 | Tee-Object -FilePath (Join-Path $stage 'manuscript-check.log')
  if ($LASTEXITCODE -ne 0) { throw 'Manuscript proof entry-point check failed.' }
  & $lakeBin --packages $overrideFile env lean Audit.lean 2>&1 | Tee-Object -FilePath (Join-Path $stage 'axioms.log')
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }
  $log = [IO.File]::ReadAllText((Join-Path $stage 'axioms.log'))
  $reports = [regex]::Matches($log, "(?s)'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
  $checked = @()
  $axiomRows = @()
  foreach ($report in $reports) {
    $checked += $report.Groups[1].Value
    $usedAxioms = @()
    foreach ($item in $report.Groups[2].Value.Split(',')) {
      $name = $item.Trim()
      if ($name -and $name -notin @('propext','Classical.choice','Quot.sound')) { throw "Unexpected axiom: $name" }
      if ($name) { $usedAxioms += $name }
    }
    $axiomRows += [ordered]@{ theorem = $report.Groups[1].Value; axioms = $usedAxioms }
  }
  foreach ($report in [regex]::Matches($log, "'([^']+)' does not depend on any axioms")) {
    $checked += $report.Groups[1].Value
    $axiomRows += [ordered]@{ theorem = $report.Groups[1].Value; axioms = @() }
  }
  if ($checked.Count -ne $names.Count -or (Compare-Object ($names | Sort-Object) ($checked | Sort-Object))) {
    throw 'Axiom audit coverage mismatch.'
  }
  [IO.File]::WriteAllText((Join-Path $stage 'axiom-summary.json'), (ConvertTo-Json -InputObject $axiomRows -Depth 5))
  $result = [ordered]@{
    status = 'full_formalization_verified'
    full_paper_proved = $true
    manuscript_sha256 = $paperHash
    coverage_sha256 = (Get-FileHash -LiteralPath $coveragePath -Algorithm SHA256).Hash.ToLowerInvariant()
    manuscript_correspondence_review = 'complete'
    principal_manuscript_results = $paperLabels.Count
    checked_manuscript_entry_points = $coveredProofs.Count
    lean = $leanVersion
    mathlib = ($manifest.packages | Where-Object name -eq 'mathlib').rev
    checked_theorems = $checked.Count
    local_lean_modules = $librarySources.Count + 1
    allowed_axioms = @('propext','Classical.choice','Quot.sound')
    sorry_count = 0
    admit_count = 0
    manuscript_specific_axioms = 0
    relative_verified = 0
    compilation_errors = 0
    fresh_local_build = [bool]$Fresh
    module_batch_size = $ModuleBatchSize
    verified_at_utc = [DateTime]::UtcNow.ToString('o')
    build_directory = $stage
  }
  [IO.File]::WriteAllText((Join-Path $stage 'result.json'), ($result | ConvertTo-Json -Depth 5))
  Write-Output "AUDIT PASS: $($checked.Count) theorems; standard axioms only. All $($paperLabels.Count) principal manuscript results verified."
} finally {
  Pop-Location
  $env:LEAN_PATH = $priorLeanPath
  if ($null -eq $priorLeanThreads) { Remove-Item Env:LEAN_NUM_THREADS -ErrorAction SilentlyContinue } else { $env:LEAN_NUM_THREADS = $priorLeanThreads }
}
