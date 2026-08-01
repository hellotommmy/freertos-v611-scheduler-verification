param(
    [ValidateRange(10, 300)]
    [int]$TimeoutSeconds = 60,

    [string]$RunId = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ'),

    [ValidateSet('drop-remove-reverse-link')]
    [string]$MutationId = 'drop-remove-reverse-link'
)

$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$runDir = Join-Path $projectRoot (Join-Path 'runs' $RunId)
$mutantPath = Join-Path $runDir 'list.mutant.c'
$binaryPath = Join-Path $runDir 'list_trace_mutant'
$manifestPath = Join-Path $runDir 'mutation.json'
$statusPath = Join-Path $runDir 'status.txt'
$commandPath = Join-Path $runDir 'command.txt'

function ConvertTo-WslPath([string]$WindowsPath) {
    $fullPath = [IO.Path]::GetFullPath($WindowsPath)
    if ($fullPath.Length -lt 3 -or $fullPath[1] -ne ':') {
        throw "Expected an absolute drive path: $WindowsPath"
    }
    $drive = $fullPath.Substring(0, 1).ToLowerInvariant()
    $rest = $fullPath.Substring(3).Replace('\', '/')
    return "/mnt/$drive/$rest"
}

function Invoke-BoundedProcess(
    [string]$FileName,
    [string[]]$ArgumentList,
    [string]$StdoutPath,
    [string]$StderrPath,
    [int]$BoundSeconds
) {
    $process = [Diagnostics.Process]::new()
    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $FileName
    $startInfo.WorkingDirectory = $projectRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    foreach ($argument in $ArgumentList) { [void]$startInfo.ArgumentList.Add($argument) }
    $process.StartInfo = $startInfo
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $timedOut = -not $process.WaitForExit($BoundSeconds * 1000)
    if ($timedOut) {
        & "$env:SystemRoot\System32\taskkill.exe" /PID $process.Id /T /F | Out-Null
        $process.WaitForExit()
    }
    Set-Content -LiteralPath $StdoutPath -Encoding utf8 -Value $stdoutTask.GetAwaiter().GetResult()
    Set-Content -LiteralPath $StderrPath -Encoding utf8 -Value $stderrTask.GetAwaiter().GetResult()
    return [pscustomobject]@{
        ExitCode = $(if ($timedOut) { 124 } else { $process.ExitCode })
        TimedOut = $timedOut
        Pid = $process.Id
    }
}

New-Item -ItemType Directory -Force -Path $runDir | Out-Null
$pythonExe = (Get-Command python -ErrorAction Stop).Source
$sourcePath = Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\list.c'
$mutationTool = Join-Path $projectRoot 'tools\mutate_source.py'
$mutationArgs = @($mutationTool, $MutationId, $sourcePath, $mutantPath)
$mutation = Invoke-BoundedProcess $pythonExe $mutationArgs $manifestPath `
    (Join-Path $runDir 'mutation.stderr.log') $TimeoutSeconds

$proofPort = ConvertTo-WslPath (Join-Path $projectRoot 'proof_port')
$includeDir = ConvertTo-WslPath (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include')
$harness = ConvertTo-WslPath (Join-Path $projectRoot 'harness\list_trace.c')
$mutant = ConvertTo-WslPath $mutantPath
$binary = ConvertTo-WslPath $binaryPath
$compileArgs = @(
    '-d', 'Ubuntu', '--exec', '/usr/bin/gcc',
    '-std=c99', '-Wall', '-Wextra', '-Werror',
    '-I', $proofPort, '-I', $includeDir,
    $harness, $mutant, '-o', $binary
)
$traceArgs = @('-d', 'Ubuntu', '--exec', $binary)
Set-Content -LiteralPath $commandPath -Encoding utf8 -Value @(
    "$pythonExe $($mutationArgs -join ' ')"
    "wsl.exe $($compileArgs -join ' ')"
    "wsl.exe $($traceArgs -join ' ')"
)

$stopwatch = [Diagnostics.Stopwatch]::StartNew()
if ($mutation.ExitCode -eq 0) {
    $compile = Invoke-BoundedProcess 'wsl.exe' $compileArgs `
        (Join-Path $runDir 'compile.stdout.log') `
        (Join-Path $runDir 'compile.stderr.log') $TimeoutSeconds
} else {
    $compile = [pscustomobject]@{ ExitCode = 125; TimedOut = $false; Pid = 0 }
}
if ($compile.ExitCode -eq 0) {
    $trace = Invoke-BoundedProcess 'wsl.exe' $traceArgs `
        (Join-Path $runDir 'trace.stdout.log') `
        (Join-Path $runDir 'trace.stderr.log') $TimeoutSeconds
} else {
    $trace = [pscustomobject]@{ ExitCode = 125; TimedOut = $false; Pid = 0 }
}
$stopwatch.Stop()

$killed = $mutation.ExitCode -eq 0 -and $compile.ExitCode -eq 0 -and `
    -not $trace.TimedOut -and $trace.ExitCode -ne 0
$status = @(
    "run_id=$RunId",
    "mutation_id=$MutationId",
    "mutation_exit_code=$($mutation.ExitCode)",
    "compile_exit_code=$($compile.ExitCode)",
    "trace_exit_code=$($trace.ExitCode)",
    "trace_timed_out=$($trace.TimedOut.ToString().ToLowerInvariant())",
    "mutation_killed=$($killed.ToString().ToLowerInvariant())",
    "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))",
    "sha256[upstream_list.c]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash)",
    "sha256[mutant_list.c]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $mutantPath).Hash)",
    "sha256[harness]=$((Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $projectRoot 'harness\list_trace.c')).Hash)"
)
Set-Content -LiteralPath $statusPath -Encoding utf8 -Value $status
Write-Output ($status -join [Environment]::NewLine)

if (-not $killed) { exit 1 }
exit 0
