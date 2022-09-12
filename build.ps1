function Get-UnixPath {
  [IO.Path]::Combine($args[0].split("/"))
}

function Parse-Deps {
  $result = @{}
  #New-Object Collections.Generic.List[String]
  foreach ($line in Get-Content $args[0]) {
    if ($line -Match "->") {
      $line = $line -Split "->" | ConvertFrom-Json
      $in_file = Get-UnixPath $line[0]
      $out_file = Get-UnixPath $line[1]
      if (-not ($result.ContainsKey($out_file))) {
        $result[$out_file] = New-Object Collections.Generic.List[String]
      }
      $result[$out_file].Add($in_file)
      #Write-Host $line[0]
    }
  }
  $result
}

function Which {
  $cmd = $args[0]
  $Out = Get-Command $cmd -ErrorAction SilentlyContinue
  if ($Out) {
    $Out
  } else {
    Get-Command "$cmd.exe" -ErrorAction SilentlyContinue
  }
}

$CoqDep = Which "coqdep"

function Parse-Proj {
  # Load a _CoqProject file
  $proj_file = $args[0]
  $Files = [ordered]@{}
  $i = 0;
  foreach($line in Get-Content $proj_file) {
    if ($i -eq 0) {
      $Cmds = $line
    } else {
      $tmp = $i - 1
      # In CoqProject we must
      $line = Get-UnixPath $line
      $Files.Add("$tmp",  $line)
    }
    $i = $i + 1
  }
  @{Files=$Files; Args=$Cmds}
}

$Proj = Parse-Proj .\_CoqProject

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
$build_dir = "_build"
$target_dir = Join-Path -Path $build_dir -ChildPath "Turing"
if (-not ( Test-Path -Path $target_dir -PathType Container )) {
  New-Item -Path $target_dir -ItemType Directory -Force
}

function Infer-Deps {
  if ($CoqDep) {
    # We do have coqdep, so we can run it
    $deps_file = Join-Path -Path $build_dir -ChildPath "deps.dot"
    # Generate the dependencies
    Invoke-Expression "$CoqDep -f _CoqProject -dumpgraph $deps_file" | Out-Null
    Parse-Deps $deps_file
  } else {
    # No coqdep installed
    # We should use the order of _CoqProject instead
    Write-Host "$CoqDep not found! No dependencies generated"
    @{}
  }
}

#$Deps = Infer-Deps
#Write-Host $Deps.Keys
$coqc = "coqc"
if ($env:COQC -ne $null) {
    $coqc = $env:COQC
}
$zip = "7z"
if ($env:ZIP -ne $null) {
    $zip = $env:ZIP
}

foreach($line in $Proj.Files.values) {
  $Command = "$coqc $($Proj.Args) $line"
  Write-Host $Command
  # Compile each file
  Invoke-Expression $Command
  $v_file = Get-Item $line
  Copy-Ext $v_file $target_dir ".v"
  Copy-Ext $v_file $target_dir ".vo"
  Copy-Ext $v_file $target_dir ".glob"
}

$out_file = Join-Path -Path (Resolve-Path $build_dir) -ChildPath "turing.zip"
pushd $build_dir
$Command = "$zip a -r -bb -tzip $out_file Turing"
dir Turing
Write-Host $Command
Invoke-Expression $Command
popd
