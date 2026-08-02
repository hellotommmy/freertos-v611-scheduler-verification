param(
    [ValidateRange(30, 3600)]
    [int]$TimeoutSeconds = 600,

    [string]$RunId = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ'),

    [ValidateSet(
        'EAL6_FreeRTOS_V611_List_Smoke',
        'EAL6_FreeRTOS_V611_Model',
        'EAL6_FreeRTOS_V611_Scheduler_Abstract_Model',
        'EAL6_FreeRTOS_V611_M0_Bridge',
        'EAL6_FreeRTOS_V611_List_Raw_Skip',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Probe',
        'EAL6_FreeRTOS_V611_List_Raw_R0_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R1_Init',
        'EAL6_FreeRTOS_V611_List_Raw_R2_Init_Item',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Prefix',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Run',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Topology',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Topology_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Frames',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Far_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Master',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Locality',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Run',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Topology',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Topology_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Frames',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Item_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Tail_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Far_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Master',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Interface',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Cycle',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Generic_Prefix',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Dynamic_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Transfer',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Splice',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Source_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Locality',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Projection',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Source_Effects',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Source',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Metadata',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Source_Effects',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Index_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Payload_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Topology_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Insert_Sequence',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_General_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Remove_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Remove_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_Per_Function',
        'EAL6_FreeRTOS_V611_Scheduler_Parse',
        'EAL6_FreeRTOS_V611_Scheduler_Tick',
        'EAL6_FreeRTOS_V611_Scheduler_Tick_Read_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay',
        'EAL6_FreeRTOS_V611_Scheduler_Roots',
        'EAL6_FreeRTOS_V611_Scheduler_Switch_Suspended_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Increment_Tick_Suspended_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Zero_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Until_No_Delay_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Model',
        'EAL6_FreeRTOS_V611_Scheduler_Raw_List_Relabel',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Write_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Read_Lenses',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Source_Footprint',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Source',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Wake_Key',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Cross_List',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Wake_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Transform',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Source',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Control_Leaves',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Source',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Post_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Layout_No_Go',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Root_Probe',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Preimage',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Initialise_Insert_Remove_Sequence',
        'EAL6_FreeRTOS_V611_Capstone_Assumption_Audit'
    )]
    [string]$Session = 'EAL6_FreeRTOS_V611_List_Smoke'
)

$ErrorActionPreference = 'Stop'

$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$theoryRoot = Join-Path $projectRoot 'theories'
$runRoot = Join-Path $projectRoot 'runs'
$runDir = Join-Path $runRoot $RunId
$isabelleHome = 'C:\Isabelle2025-2\Isabelle2025-2'
$isabelleTool = Join-Path $isabelleHome 'bin\isabelle'
$cygwinBash = Join-Path $isabelleHome 'contrib\cygwin\bin\bash.exe'
$autoCorresRoot = 'C:\afp25\afp-2026-07-21\thys\AutoCorres2'
$simplRoot = 'C:\afp25\afp-2026-07-21\thys\Simpl'
$wordLibRoot = 'C:\afp25\afp-2026-07-21\thys\Word_Lib'
$preparePatchedAutoCorres = Join-Path $PSScriptRoot 'prepare-patched-autocorres2.ps1'
$artifactBuild = Join-Path $projectRoot 'artifacts\frozen_p2_layout\build_and_check.ps1'
$artifactLedger = Join-Path $projectRoot 'artifacts\frozen_p2_layout\output\layout_ledger.json'
$artifactElf = Join-Path $projectRoot 'artifacts\frozen_p2_layout\output\frozen_p2_layout.elf'
$addressGenerator = Join-Path $projectRoot 'tools\generate_p2_root_address_config.py'
$generatedAddressConfig = Join-Path $projectRoot 'build\generated\P2_Root_Address_Config.ML'
$expectedArtifactElfSha256 =
    'dc830e50513384d712e0d1c68cb198ea656365f673d021c452d7d7ebd45c045a'
$isabelleHomeUser = Join-Path $env:USERPROFILE '.isabelle\Isabelle2025-2'
$session = $Session

foreach ($required in @(
    $isabelleTool, $cygwinBash, $autoCorresRoot, $simplRoot, $wordLibRoot,
    $preparePatchedAutoCorres, $artifactBuild, $addressGenerator,
    $theoryRoot
)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw "Required path is missing: $required"
    }
}

$artifactBuildOutput = & $artifactBuild -TimeoutSeconds 120

$addressGeneratorOutput = & python $addressGenerator `
    --project-root $projectRoot `
    --ledger $artifactLedger `
    --elf $artifactElf `
    --expected-elf-sha256 $expectedArtifactElfSha256 `
    --output $generatedAddressConfig
if ($LASTEXITCODE -ne 0) {
    throw "Generating the CParser address configuration failed with exit code $LASTEXITCODE"
}

$artifactElfSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $artifactElf).Hash
$artifactLedgerSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $artifactLedger).Hash
$generatedAddressConfigSha256 =
    (Get-FileHash -Algorithm SHA256 -LiteralPath $generatedAddressConfig).Hash

$patchedAutoCorresOutput = & $preparePatchedAutoCorres
$patchedAutoCorresRoot =
    (Resolve-Path -LiteralPath ($patchedAutoCorresOutput | Select-Object -Last 1)).Path

New-Item -ItemType Directory -Force -Path $runDir | Out-Null

$stdoutPath = Join-Path $runDir 'stdout.log'
$stderrPath = Join-Path $runDir 'stderr.log'
$statusPath = Join-Path $runDir 'status.txt'
$commandPath = Join-Path $runDir 'command.txt'

function ConvertTo-CygwinPath([string]$WindowsPath) {
    $fullPath = [IO.Path]::GetFullPath($WindowsPath)
    if ($fullPath -notmatch '^[A-Za-z]:\\') {
        throw "Expected an absolute drive path: $WindowsPath"
    }
    $drive = $fullPath.Substring(0, 1).ToLowerInvariant()
    $rest = $fullPath.Substring(3).Replace('\', '/')
    return "/cygdrive/$drive/$rest"
}

$isabelleToolCygwin = ConvertTo-CygwinPath $isabelleTool
$patchedAutoCorresRootCygwin = ConvertTo-CygwinPath $patchedAutoCorresRoot
$simplRootCygwin = ConvertTo-CygwinPath $simplRoot
$wordLibRootCygwin = ConvertTo-CygwinPath $wordLibRoot
$theoryRootCygwin = ConvertTo-CygwinPath $theoryRoot
$bashCommand = "exec '$isabelleToolCygwin' build " +
    "-d '$simplRootCygwin' -d '$wordLibRootCygwin' " +
    "-d '$patchedAutoCorresRootCygwin' -d '$theoryRootCygwin' " +
    "-o quick_and_dirty=false -j 1 '$session'"
Set-Content -LiteralPath $commandPath -Encoding utf8 -Value (
    "`"$cygwinBash`" --login -c `"$bashCommand`""
)

$stopwatch = [Diagnostics.Stopwatch]::StartNew()
$timedOut = $false
$process = [Diagnostics.Process]::new()
$startInfo = [Diagnostics.ProcessStartInfo]::new()
$startInfo.FileName = $cygwinBash
$startInfo.WorkingDirectory = $projectRoot
$startInfo.UseShellExecute = $false
$startInfo.CreateNoWindow = $true
$startInfo.RedirectStandardOutput = $true
$startInfo.RedirectStandardError = $true
$startInfo.Environment['CHERE_INVOKING'] = 'true'
$startInfo.Environment['LANG'] = 'en_US.UTF-8'
[void]$startInfo.ArgumentList.Add('--login')
[void]$startInfo.ArgumentList.Add('-c')
[void]$startInfo.ArgumentList.Add($bashCommand)
$process.StartInfo = $startInfo

try {
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()

    if (-not $process.WaitForExit($TimeoutSeconds * 1000)) {
        $timedOut = $true
        & "$env:SystemRoot\System32\taskkill.exe" /PID $process.Id /T /F | Out-Null
        $process.WaitForExit()
    }

    Set-Content -LiteralPath $stdoutPath -Encoding utf8 -Value (
        $stdoutTask.GetAwaiter().GetResult()
    )
    Set-Content -LiteralPath $stderrPath -Encoding utf8 -Value (
        $stderrTask.GetAwaiter().GetResult()
    )
}
finally {
    $stopwatch.Stop()
}

$exitCode = if ($timedOut) { 124 } else { $process.ExitCode }
$stdoutHash = if (Test-Path -LiteralPath $stdoutPath) {
    (Get-FileHash -Algorithm SHA256 -LiteralPath $stdoutPath).Hash
} else { 'MISSING' }
$stderrHash = if (Test-Path -LiteralPath $stderrPath) {
    (Get-FileHash -Algorithm SHA256 -LiteralPath $stderrPath).Hash
} else { 'MISSING' }

$status = @(
    "run_id=$RunId",
    "session=$session",
    "pid=$($process.Id)",
    "quick_and_dirty=false",
    "timeout_seconds=$TimeoutSeconds",
    "timed_out=$($timedOut.ToString().ToLowerInvariant())",
    "exit_code=$exitCode",
    "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))",
    "stdout_sha256=$stdoutHash",
    "stderr_sha256=$stderrHash",
    "isabelle_home_user=%USERPROFILE%/.isabelle/Isabelle2025-2"
    "frozen_layout_elf_sha256=$artifactElfSha256"
    "frozen_layout_ledger_sha256=$artifactLedgerSha256"
    "generated_address_config_sha256=$generatedAddressConfigSha256"
)
Set-Content -LiteralPath $statusPath -Encoding utf8 -Value $status

Write-Output "run_dir=$runDir"
Write-Output "exit_code=$exitCode"
Write-Output "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"

exit $exitCode
