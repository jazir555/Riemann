$c = [IO.File]::ReadAllText('C:\Users\mmeadow\Documents\Lean\mathlib4\riemann hypothesis.lean')
$lines = $c -split "`n"
Write-Host "Line 8290:"
Write-Host $lines[8289]
Write-Host "---"
Write-Host "Line 8291:"
Write-Host $lines[8290]
