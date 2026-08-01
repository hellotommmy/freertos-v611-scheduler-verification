param(
    [ValidateRange(10, 300)]
    [int]$TimeoutSeconds = 60,

    [string]$RunId = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ')
)

$ErrorActionPreference = 'Stop'

$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$runDir = Join-Path $projectRoot (Join-Path 'runs' $RunId)
$binaryPath = Join-Path $runDir 'list_trace'
$compileStdout = Join-Path $runDir 'compile.stdout.log'
$compileStderr = Join-Path $runDir 'compile.stderr.log'
$traceStdout = Join-Path $runDir 'trace.jsonl'
$traceStderr = Join-Path $runDir 'trace.stderr.log'
$analysisStdout = Join-Path $runDir 'analysis.json'
$analysisStderr = Join-Path $runDir 'analysis.stderr.log'
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
    foreach ($argument in $ArgumentList) {
        [void]$startInfo.ArgumentList.Add($argument)
    }
    $process.StartInfo = $startInfo
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $timedOut = -not $process.WaitForExit($BoundSeconds * 1000)
    if ($timedOut) {
        & "$env:SystemRoot\System32\taskkill.exe" /PID $process.Id /T /F | Out-Null
        $process.WaitForExit()
    }
    Set-Content -LiteralPath $StdoutPath -Encoding utf8 -Value (
        $stdoutTask.GetAwaiter().GetResult()
    )
    Set-Content -LiteralPath $StderrPath -Encoding utf8 -Value (
        $stderrTask.GetAwaiter().GetResult()
    )
    return [pscustomobject]@{
        ExitCode = $(if ($timedOut) { 124 } else { $process.ExitCode })
        TimedOut = $timedOut
        Pid = $process.Id
    }
}

New-Item -ItemType Directory -Force -Path $runDir | Out-Null

$proofPort = ConvertTo-WslPath (Join-Path $projectRoot 'proof_port')
$includeDir = ConvertTo-WslPath (
    Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include'
)
$harness = ConvertTo-WslPath (Join-Path $projectRoot 'harness\list_trace.c')
$listSource = ConvertTo-WslPath (
    Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\list.c'
)
$binary = ConvertTo-WslPath $binaryPath

$compileArguments = @(
    '-d', 'Ubuntu', '--exec', '/usr/bin/gcc',
    '-std=c99', '-Wall', '-Wextra', '-Werror',
    '-I', $proofPort, '-I', $includeDir,
    $harness, $listSource, '-o', $binary
)
$traceArguments = @('-d', 'Ubuntu', '--exec', $binary)
$analysisTool = Join-Path $projectRoot 'tools\analyse_list_trace.py'
$analysisArguments = @($analysisTool, $traceStdout, '--require-core-witnesses')
$pythonExe = (Get-Command python -ErrorAction Stop).Source
Set-Content -LiteralPath $commandPath -Encoding utf8 -Value @(
    "wsl.exe $($compileArguments -join ' ')"
    "wsl.exe $($traceArguments -join ' ')"
    "$pythonExe $($analysisArguments -join ' ')"
)

$stopwatch = [Diagnostics.Stopwatch]::StartNew()
$compile = Invoke-BoundedProcess 'wsl.exe' $compileArguments `
    $compileStdout $compileStderr $TimeoutSeconds
if ($compile.ExitCode -eq 0) {
    $trace = Invoke-BoundedProcess 'wsl.exe' $traceArguments `
        $traceStdout $traceStderr $TimeoutSeconds
} else {
    $trace = [pscustomobject]@{ ExitCode = 125; TimedOut = $false; Pid = 0 }
    Set-Content -LiteralPath $traceStdout -Encoding utf8 -Value ''
    Set-Content -LiteralPath $traceStderr -Encoding utf8 -Value 'not run'
}
if ($trace.ExitCode -eq 0) {
    $analysis = Invoke-BoundedProcess $pythonExe $analysisArguments `
        $analysisStdout $analysisStderr $TimeoutSeconds
} else {
    $analysis = [pscustomobject]@{ ExitCode = 125; TimedOut = $false; Pid = 0 }
    Set-Content -LiteralPath $analysisStdout -Encoding utf8 -Value ''
    Set-Content -LiteralPath $analysisStderr -Encoding utf8 -Value 'not run'
}
$stopwatch.Stop()

$filesToHash = @(
    'harness\list_trace.c',
    'upstream\FreeRTOSV6.1.1\Source\list.c',
    'proof_port\FreeRTOSConfig.h',
    'proof_port\portmacro.h'
)
$status = @(
    "run_id=$RunId",
    "compile_pid=$($compile.Pid)",
    "compile_exit_code=$($compile.ExitCode)",
    "compile_timed_out=$($compile.TimedOut.ToString().ToLowerInvariant())",
    "trace_pid=$($trace.Pid)",
    "trace_exit_code=$($trace.ExitCode)",
    "trace_timed_out=$($trace.TimedOut.ToString().ToLowerInvariant())",
    "analysis_pid=$($analysis.Pid)",
    "analysis_exit_code=$($analysis.ExitCode)",
    "analysis_timed_out=$($analysis.TimedOut.ToString().ToLowerInvariant())",
    "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"
)
foreach ($file in $filesToHash) {
    $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath (
        Join-Path $projectRoot $file
    )).Hash
    $status += "sha256[$file]=$hash"
}
if (Test-Path -LiteralPath $binaryPath) {
    $status += "sha256[binary]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $binaryPath).Hash)"
}
$status += "sha256[trace]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $traceStdout).Hash)"
$status += "sha256[analysis]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $analysisStdout).Hash)"
Set-Content -LiteralPath $statusPath -Encoding utf8 -Value $status

Write-Output "run_dir=$runDir"
Write-Output "compile_exit_code=$($compile.ExitCode)"
Write-Output "trace_exit_code=$($trace.ExitCode)"
Write-Output "analysis_exit_code=$($analysis.ExitCode)"
Write-Output "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"

if ($compile.ExitCode -ne 0) { exit $compile.ExitCode }
if ($trace.ExitCode -ne 0) { exit $trace.ExitCode }
exit $analysis.ExitCode
