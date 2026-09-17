param(
  [string]$PackageRoot = 'E:\Lean 4\Sendov_conjecture_explicit_n0\.lake\packages',
  [switch]$Fresh
)
$ErrorActionPreference = 'Stop'
$leanVersion = 'v4.34.0-rc1'
$lakeBin = Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---$leanVersion\bin\lake.exe"
if (!(Test-Path -LiteralPath $lakeBin)) { throw "Missing Lean toolchain $leanVersion" }
$sources = @(Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'ModifiedCartan') -Filter '*.lean' -File -Recurse)
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
$suffix = if ($Fresh) { [guid]::NewGuid().ToString('N') } else { 'verified' }
$stage = Join-Path $env:TEMP ('ModifiedCartan-' + $suffix)
[IO.Directory]::CreateDirectory($stage) | Out-Null
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
$overrides = @()
foreach ($package in $manifest.packages) {
  $path = Join-Path $PackageRoot $package.name
  $rev = (& git -C $path rev-parse HEAD | Out-String).Trim()
  if ($LASTEXITCODE -ne 0 -or $rev -ne $package.rev) {
    throw "Dependency revision mismatch: $($package.name)"
  }
  $overrides += [ordered]@{
    name = $package.name; scope = $package.scope; type = 'path'; dir = $path
    inherited = $package.inherited; configFile = $package.configFile; manifestFile = $package.manifestFile
  }
}
$overrideFile = Join-Path $stage 'local-packages.json'
[IO.File]::WriteAllText($overrideFile, (ConvertTo-Json -InputObject @{
  schemaVersion = '1.2.0'; packages = $overrides
} -Depth 10))
$inputs = $sources + @(Get-ChildItem -LiteralPath $PSScriptRoot -File | Where-Object {
  $_.Extension -eq '.lean' -or $_.Name -in @('lakefile.toml','lean-toolchain','lake-manifest.json')
})
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
  & $lakeBin --packages $overrideFile build 2>&1 | Tee-Object -FilePath (Join-Path $stage 'build.log')
  if ($LASTEXITCODE -ne 0) { throw 'Lake build failed.' }
  & $lakeBin --packages $overrideFile env lean Audit.lean 2>&1 | Tee-Object -FilePath (Join-Path $stage 'axioms.log')
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }
  $log = [IO.File]::ReadAllText((Join-Path $stage 'axioms.log'))
  $reports = [regex]::Matches($log, "(?s)'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
  $checked = @()
  foreach ($report in $reports) {
    $checked += $report.Groups[1].Value
    foreach ($item in $report.Groups[2].Value.Split(',')) {
      $name = $item.Trim()
      if ($name -and $name -notin @('propext','Classical.choice','Quot.sound')) {
        throw "Unexpected axiom: $name"
      }
    }
  }
  if ($reports.Count -ne $names.Count -or (Compare-Object ($names | Sort-Object) ($checked | Sort-Object))) {
    throw 'Axiom audit coverage mismatch.'
  }
  $result = [ordered]@{
    status = 'partial_formalization_verified'
    full_paper_proved = $false
    lean = $leanVersion
    mathlib = ($manifest.packages | Where-Object name -eq 'mathlib').rev
    checked_theorems = $checked.Count
    allowed_axioms = @('propext','Classical.choice','Quot.sound')
    verified_at_utc = [DateTime]::UtcNow.ToString('o')
    build_directory = $stage
  }
  [IO.File]::WriteAllText((Join-Path $stage 'result.json'), ($result | ConvertTo-Json -Depth 5))
  Write-Output "AUDIT PASS: $($checked.Count) theorems; standard axioms only. Full paper: NOT YET PROVED."
} finally {
  Pop-Location
  $env:LEAN_PATH = $priorLeanPath
  if ($null -eq $priorLeanThreads) {
    Remove-Item Env:LEAN_NUM_THREADS -ErrorAction SilentlyContinue
  } else {
    $env:LEAN_NUM_THREADS = $priorLeanThreads
  }
}
