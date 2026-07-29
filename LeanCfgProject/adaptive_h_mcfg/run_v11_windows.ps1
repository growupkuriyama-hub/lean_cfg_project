param(
  [Parameter(Mandatory=$true)][string]$DemoRoot,
  [string]$Output = ".\mcfg-v11-experiment",
  [int]$Runs = 5,
  [int]$Seeds = 5,
  [switch]$Minimal,
  [switch]$SkipCollection
)

$ErrorActionPreference = "Stop"
$ScriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$ArgsList = @(
  "$ScriptRoot\run_v11_end_to_end.py",
  $DemoRoot,
  "--output", $Output,
  "--runs", "$Runs",
  "--seeds", "$Seeds"
)
if ($Minimal) { $ArgsList += "--minimal" }
if ($SkipCollection) { $ArgsList += "--skip-collection" }

python @ArgsList
if ($LASTEXITCODE -ne 0) { throw "V11 experiment failed with exit code $LASTEXITCODE" }
Write-Host "V11 experiment complete: $Output"
