param([string]$Path)
$enc = New-Object System.Text.UTF8Encoding $false
$full = [System.IO.Path]::GetFullPath($Path)
$t = [System.IO.File]::ReadAllText($full)
$t2 = $t.TrimStart([char]0xFEFF)
if ($t -ne $t2) { [System.IO.File]::WriteAllText($full, $t2, $enc); "stripped BOM: $Path" } else { "no BOM: $Path" }
