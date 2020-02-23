
$Files = [ordered]@{}
$i = 0;
foreach($line in Get-Content .\_CoqProject) {
  if ($i -eq 0) {
    Set-Variable -Name "Args" -Value $line
  } else {
    $tmp = $i - 1
    $Files.Add("$tmp", $line)
  }
  $i = $i + 1
}
function Get-OldExt {
  $file = $args[0]
  $ext = $args[1]
  Join-Path -Path $file.Directory -ChildPath "$($file.BaseName)$ext"
}

function Copy-Ext {
  $file = $args[0]
  $target = $args[1]
  $ext = $args[2]
  $src = Join-Path -Path $file.Directory -ChildPath "$($file.BaseName)$ext"
  $dst = Join-Path -Path $target -ChildPath "$($file.BaseName)$ext"
  Write-Host "copy $src $dst"
  Copy-Item $src $dst
}

# Create a _build/Turing directory
New-Item -Path "_build/Turing" -ItemType Directory -Force
$target_dir = Get-Item "_build/Turing"

foreach($line in $Files.values) {
  $Command = "coqc $Args $line"
  Write-Host $Command
  # Compile each file
  Invoke-Expression $Command
  $v_file = Get-Item $line
  Copy-Ext $v_file $target_dir ".v"
  Copy-Ext $v_file $target_dir ".vo"
  Copy-Ext $v_file $target_dir ".glob"
}

& {
  cd _build;
  7z -r a turing.zip Turing
  cd ..
}