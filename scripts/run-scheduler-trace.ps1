param(
    [ValidateRange(10, 300)]
    [int]$TimeoutSeconds = 60,

    [string]$RunId = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ')
)

$ErrorActionPreference = 'Stop'

$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$runDir = Join-Path $projectRoot (Join-Path 'runs' $RunId)
$binaryPath = Join-Path $runDir 'scheduler_trace'
$compileStdout = Join-Path $runDir 'compile.stdout.log'
$compileStderr = Join-Path $runDir 'compile.stderr.log'
$traceStdout = Join-Path $runDir 'trace.jsonl'
$traceStderr = Join-Path $runDir 'trace.stderr.log'
$analysisPath = Join-Path $runDir 'analysis.json'
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
        & "$env:SystemRoot\System32\taskkill.exe" /PID $process.Id /T /F |
            Out-Null
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

function Test-Trace([string]$TracePath) {
    $records = @()
    $lineNumber = 0
    foreach ($line in Get-Content -LiteralPath $TracePath) {
        ++$lineNumber
        if ([string]::IsNullOrWhiteSpace($line)) {
            continue
        }
        try {
            $records += $line | ConvertFrom-Json -ErrorAction Stop
        } catch {
            throw "Invalid JSONL at line ${lineNumber}: $($_.Exception.Message)"
        }
    }

    $requiredScenarios = @(
        'tick_no_wake',
        'tick_wakes_delayed',
        'tick_wrap_swaps_delay_roles',
        'same_priority_switch_fifo',
        'delay_positive_no_wrap',
        'delay_positive_wrap'
    )
    $seenScenarios = @(
        $records |
            Where-Object { $_.kind -eq 'snapshot' } |
            ForEach-Object { $_.scenario } |
            Sort-Object -Unique
    )
    $missing = @($requiredScenarios | Where-Object { $_ -notin $seenScenarios })
    $failedChecks = @(
        $records | Where-Object { $_.kind -eq 'check' -and $_.ok -ne $true }
    )
    $fatalRecords = @(
        $records |
            Where-Object { $_.kind -in @('stub_reached', 'invariant_failure') }
    )
    $summary = @(
        $records |
            Where-Object {
                $_.kind -eq 'check' -and
                $_.id -eq 'all.required.scenarios.completed' -and
                $_.ok -eq $true
            }
    )
    $meta = @($records | Where-Object { $_.kind -eq 'meta' })

    if ($meta.Count -ne 1) { throw "Expected exactly one meta record" }
    if ($missing.Count -ne 0) {
        throw "Missing required scenarios: $($missing -join ', ')"
    }
    if ($failedChecks.Count -ne 0) {
        throw "Trace contains $($failedChecks.Count) failed checks"
    }
    if ($fatalRecords.Count -ne 0) {
        throw "Trace reached a stub or invariant failure"
    }
    if ($summary.Count -ne 1) {
        throw "Missing unique successful completion record"
    }

    return [ordered]@{
        ok = $true
        record_count = $records.Count
        snapshot_count = @(
            $records | Where-Object { $_.kind -eq 'snapshot' }
        ).Count
        check_count = @(
            $records | Where-Object { $_.kind -eq 'check' }
        ).Count
        scenarios = $seenScenarios
        fatal_record_count = $fatalRecords.Count
    }
}

New-Item -ItemType Directory -Force -Path $runDir | Out-Null

$proofScheduler = ConvertTo-WslPath (
    Join-Path $projectRoot 'proof_port\scheduler'
)
$includeDir = ConvertTo-WslPath (
    Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include'
)
$harness = ConvertTo-WslPath (
    Join-Path $projectRoot 'harness\scheduler_trace.c'
)
$binary = ConvertTo-WslPath $binaryPath

$compileArguments = @(
    '-d', 'Ubuntu', '--exec', '/usr/bin/gcc',
    '-std=c99', '-Wall', '-Wextra', '-Werror', '-fno-strict-aliasing',
    '-iquote', $proofScheduler, '-I', $includeDir,
    $harness, '-o', $binary
)
$traceArguments = @('-d', 'Ubuntu', '--exec', $binary)

Set-Content -LiteralPath $commandPath -Encoding utf8 -Value @(
    "wsl.exe $($compileArguments -join ' ')"
    "wsl.exe $($traceArguments -join ' ')"
    'PowerShell JSONL gate: parse every record; require six scenarios, all checks, no stub/fatal record'
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

$analysisExitCode = 125
if ($trace.ExitCode -eq 0) {
    try {
        $analysis = Test-Trace $traceStdout
        $analysis | ConvertTo-Json -Depth 5 |
            Set-Content -LiteralPath $analysisPath -Encoding utf8
        $analysisExitCode = 0
    } catch {
        [ordered]@{ ok = $false; error = $_.Exception.Message } |
            ConvertTo-Json -Depth 5 |
            Set-Content -LiteralPath $analysisPath -Encoding utf8
        $analysisExitCode = 1
    }
} else {
    [ordered]@{ ok = $false; error = 'trace not run' } |
        ConvertTo-Json -Depth 5 |
        Set-Content -LiteralPath $analysisPath -Encoding utf8
}
$stopwatch.Stop()

$filesToHash = @(
    'harness\scheduler_trace.c',
    'scripts\run-scheduler-trace.ps1',
    'proof_port\scheduler\FreeRTOSConfig.h',
    'proof_port\scheduler\scheduler_port_contract.h',
    'proof_port\scheduler\scheduler_port_contract.c',
    'upstream\FreeRTOSV6.1.1\Source\tasks.c',
    'upstream\FreeRTOSV6.1.1\Source\list.c'
)
$status = @(
    "run_id=$RunId",
    "compile_pid=$($compile.Pid)",
    "compile_exit_code=$($compile.ExitCode)",
    "compile_timed_out=$($compile.TimedOut.ToString().ToLowerInvariant())",
    "trace_pid=$($trace.Pid)",
    "trace_exit_code=$($trace.ExitCode)",
    "trace_timed_out=$($trace.TimedOut.ToString().ToLowerInvariant())",
    "analysis_exit_code=$analysisExitCode",
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
$status += "sha256[analysis]=$((Get-FileHash -Algorithm SHA256 -LiteralPath $analysisPath).Hash)"
Set-Content -LiteralPath $statusPath -Encoding utf8 -Value $status

Write-Output "run_dir=$runDir"
Write-Output "compile_exit_code=$($compile.ExitCode)"
Write-Output "trace_exit_code=$($trace.ExitCode)"
Write-Output "analysis_exit_code=$analysisExitCode"
Write-Output "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"

if ($compile.ExitCode -ne 0) { exit $compile.ExitCode }
if ($trace.ExitCode -ne 0) { exit $trace.ExitCode }
exit $analysisExitCode
