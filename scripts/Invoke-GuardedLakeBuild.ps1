# Guarded `lake build` wrapper with STALE-LOCK AUTOCLEAR.
#
# Usage (agents: ONE call replaces the hand-rolled lock protocol):
#   pwsh -File scripts/Invoke-GuardedLakeBuild.ps1 -Module zeta_rigorous
#
# Protocol:
#   1. Atomically create .lake_build_lock (exclusive New-Item). On success,
#      stamp it with "<PID> <ISO-timestamp>" so release is owner-checked.
#   2. If the lock exists: when its age exceeds -StaleMinutes (default 25)
#      AND no live lake/lean processes run, it is stale -> AUTOCLEAR
#      (delete + log) and retry immediately. Otherwise sleep -RetrySec
#      (default 60) until -MaxWaitSec (default 3h), then GUARD-TIMEOUT.
#   3. Run the build (default `lake build <Module>`), tee output to a
#      timestamped log under -LogDir, print BUILD-EXIT=<n>.
#   4. Release ONLY if the lock still carries our PID (re-verified after
#      the long build); never delete another owner's live lock.
#
# Markers printed for coordinator grepping:
#   GUARD-ACQUIRED | GUARD-AUTOCLEARED <age-min> | GUARD-WAIT <age-min>
#   GUARD-TIMEOUT | GUARD-RELEASED | GUARD-RELEASE-SKIPPED <reason>
#   BUILD-EXIT=<n> | BUILD-LOG=<path>
param(
  [Parameter(Mandatory = $true)][string]$Module,
  [int]$StaleMinutes = 25,
  [int]$RetrySec = 60,
  [int]$MaxWaitSec = 10800,
  [string]$LogDir = (Join-Path ([System.IO.Path]::GetTempPath()) "kilo"),
  [string]$LockPath = ".lake_build_lock",
  [string]$CommandOverride = "",
  [string[]]$ProcessNames = @("lake", "lean")
)

$ErrorActionPreference = "Stop"
$myPid = [System.Diagnostics.Process]::GetCurrentProcess().Id
$deadline = (Get-Date).AddSeconds($MaxWaitSec)
$acquired = $false

function Get-LockAgeMin {
  try {
    $item = Get-Item -LiteralPath $LockPath -ErrorAction Stop
    return ((Get-Date) - $item.LastWriteTime).TotalMinutes
  } catch { return -1 }
}

function Test-LiveBuilders {
  return ($null -ne (Get-Process -Name $ProcessNames -ErrorAction SilentlyContinue))
}

while (-not $acquired) {
  try {
    New-Item -Path $LockPath -ItemType File -ErrorAction Stop | Out-Null
    Set-Content -LiteralPath $LockPath -Value "$myPid $((Get-Date).ToString('o'))"
    $acquired = $true
    Write-Output "GUARD-ACQUIRED pid=$myPid"
  } catch {
    $age = Get-LockAgeMin
    if ((Get-Date) -gt $deadline) {
      Write-Output ("GUARD-TIMEOUT waited, lock age {0:N1} min" -f $age)
      exit 2
    }
    if ($age -gt $StaleMinutes -and -not (Test-LiveBuilders)) {
      Write-Output ("GUARD-AUTOCLEARED age {0:N1} min, no live lake/lean" -f $age)
      Remove-Item -LiteralPath $LockPath -Force -ErrorAction SilentlyContinue
      continue
    }
    Write-Output ("GUARD-WAIT lock age {0:N1} min, retry in {1}s" -f $age, $RetrySec)
    Start-Sleep -Seconds $RetrySec
  }
}

$stamp = (Get-Date).ToString("yyyyMMdd-HHmmss")
$logFile = Join-Path $LogDir "guarded-build-$Module-$stamp.log"
try {
  if ($LogDir -ne "" -and -not (Test-Path -LiteralPath $LogDir)) {
    New-Item -Path $LogDir -ItemType Directory -Force | Out-Null
  }
  if ($CommandOverride -ne "") {
    $out = Invoke-Expression $CommandOverride 2>&1 | Tee-Object -FilePath $logFile
    Write-Output $out
    $code = 0
  } else {
    $out = & lake build $Module 2>&1 | Tee-Object -FilePath $logFile
    Write-Output $out
    $code = $LASTEXITCODE
  }
  Write-Output "BUILD-EXIT=$code"
  Write-Output "BUILD-LOG=$logFile"
  exit $code
} finally {
  $owner = ""
  try { $owner = (Get-Content -LiteralPath $LockPath -ErrorAction Stop | Select-Object -First 1) } catch { $owner = "" }
  if ($owner -match "^$myPid\b") {
    Remove-Item -LiteralPath $LockPath -Force -ErrorAction SilentlyContinue
    Write-Output "GUARD-RELEASED pid=$myPid"
  } else {
    Write-Output "GUARD-RELEASE-SKIPPED owner='$owner' mine='$myPid'"
  }
}
