param(
    [ValidateRange(30, 300)]
    [int]$TimeoutSeconds = 120,

    [ValidateNotNullOrEmpty()]
    [string]$WslDistribution = 'Ubuntu'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$artifactDir = $PSScriptRoot
$projectRoot = (Resolve-Path (Join-Path $artifactDir '..\..')).Path
$canonicalProjectRoot = '/workspace/freertos_v611_scheduler'
$outputDir = Join-Path $artifactDir 'output'
$rawDir = Join-Path $outputDir 'raw'
New-Item -ItemType Directory -Force -Path $outputDir, $rawDir | Out-Null

$translationUnit = Join-Path $projectRoot 'proof_port\scheduler\scheduler_translation_unit.c'
$linkStubs = Join-Path $artifactDir 'link_stubs.c'
$linkerScript = Join-Path $artifactDir 'frozen_p2_layout.ld'
$translationObject = Join-Path $outputDir 'scheduler_translation_unit.o'
$stubsObject = Join-Path $outputDir 'link_stubs.o'
$elfPath = Join-Path $outputDir 'frozen_p2_layout.elf'
$reproElfPath = Join-Path $outputDir 'frozen_p2_layout.repro.elf'
$mapPath = Join-Path $outputDir 'frozen_p2_layout.map'
$reproMapPath = Join-Path $outputDir 'frozen_p2_layout.repro.map'
$ledgerPath = Join-Path $outputDir 'layout_ledger.json'
$reportPath = Join-Path $outputDir 'layout_report.txt'
$hashesPath = Join-Path $outputDir 'hashes.sha256'
$commandsPath = Join-Path $outputDir 'commands.txt'
$failurePath = Join-Path $outputDir 'build_failure.txt'

$utf8NoBom = [Text.UTF8Encoding]::new($false)
$commandRecords = [Collections.Generic.List[string]]::new()
$runRecords = [Collections.Generic.List[object]]::new()
$stopwatch = [Diagnostics.Stopwatch]::StartNew()

function Write-Utf8([string]$Path, [string]$Text) {
    [IO.File]::WriteAllText($Path, $Text, $utf8NoBom)
}

function ConvertTo-WslPath([string]$WindowsPath) {
    $fullPath = [IO.Path]::GetFullPath($WindowsPath)
    if ($fullPath.Length -lt 3 -or $fullPath[1] -ne ':') {
        throw "Expected an absolute drive path: $WindowsPath"
    }
    $drive = $fullPath.Substring(0, 1).ToLowerInvariant()
    $rest = $fullPath.Substring(3).Replace('\', '/')
    return "/mnt/$drive/$rest"
}

function Format-CommandArgument([string]$Argument) {
    if ($Argument -match '[\s"]') {
        return '"' + $Argument.Replace('"', '\"') + '"'
    }
    return $Argument
}

function Invoke-BoundedWsl(
    [string]$Label,
    [string]$Tool,
    [string[]]$Arguments,
    [string]$StdoutPath,
    [string]$StderrPath
) {
    $wslArguments = @(
        '-d', $WslDistribution, '--exec', '/usr/bin/env',
        'SOURCE_DATE_EPOCH=0', 'LC_ALL=C', 'TZ=UTC', $Tool
    ) + $Arguments

    $display = 'wsl.exe ' + (($wslArguments | ForEach-Object {
        Format-CommandArgument $_
    }) -join ' ')
    $commandRecords.Add("[$Label] $display")

    $process = [Diagnostics.Process]::new()
    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = 'wsl.exe'
    $startInfo.WorkingDirectory = $projectRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    foreach ($argument in $wslArguments) {
        [void]$startInfo.ArgumentList.Add($argument)
    }
    $process.StartInfo = $startInfo

    $commandStopwatch = [Diagnostics.Stopwatch]::StartNew()
    [void]$process.Start()
    $processId = $process.Id
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $timedOut = -not $process.WaitForExit($TimeoutSeconds * 1000)
    if ($timedOut) {
        & "$env:SystemRoot\System32\taskkill.exe" /PID $processId /T /F | Out-Null
        $process.WaitForExit()
    }
    $commandStopwatch.Stop()

    $stdout = $stdoutTask.GetAwaiter().GetResult().Replace("`0", '')
    $stderr = $stderrTask.GetAwaiter().GetResult().Replace("`0", '')
    Write-Utf8 $StdoutPath $stdout
    Write-Utf8 $StderrPath $stderr
    $exitCode = if ($timedOut) { 124 } else { $process.ExitCode }
    $record = [pscustomobject]@{
        label = $Label
        exit_code = $exitCode
        timed_out = $timedOut
        stdout = [IO.Path]::GetRelativePath($projectRoot, $StdoutPath).Replace('\', '/')
        stderr = [IO.Path]::GetRelativePath($projectRoot, $StderrPath).Replace('\', '/')
    }
    $runRecords.Add($record)
    if ($exitCode -ne 0) {
        throw "$Label failed with exit code $exitCode; see $StderrPath"
    }
    return $record
}

function Get-Sha256([string]$Path) {
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-RelativePath([string]$Path) {
    return [IO.Path]::GetRelativePath($projectRoot, $Path).Replace('\', '/')
}

function ConvertTo-CanonicalEvidenceText([string]$Text) {
    $normalised = $Text.Replace($projectRootWsl, $canonicalProjectRoot)
    $normalised = $normalised.Replace($projectRoot.Replace('\', '/'), $canonicalProjectRoot)
    $normalised = $normalised.Replace($projectRoot, $canonicalProjectRoot)
    return $normalised.Replace("`r`n", "`n").Replace("`r", "`n")
}

function ConvertTo-CanonicalCommandText([string]$Text) {
    $normalised = ConvertTo-CanonicalEvidenceText $Text
    $distributionArgument = Format-CommandArgument $WslDistribution
    $actualPrefix = "wsl.exe -d $distributionArgument --exec"
    return $normalised.Replace(
        $actualPrefix,
        'wsl.exe -d <wsl-distribution> --exec'
    )
}

function Normalize-TextEvidenceFile([string]$Path) {
    $text = Get-Content -Raw -LiteralPath $Path
    Write-Utf8 $Path (ConvertTo-CanonicalEvidenceText $text)
}

function Get-ReadelfObjects([string]$Text, [string[]]$Names) {
    $wanted = @{}
    foreach ($name in $Names) { $wanted[$name] = $true }
    $result = @{}
    foreach ($line in $Text -split "`r?`n") {
        $match = [regex]::Match(
            $line,
            '^\s*\d+:\s+([0-9A-Fa-f]+)\s+(\d+)\s+OBJECT\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$'
        )
        if (-not $match.Success) { continue }
        $name = $match.Groups[6].Value
        if (-not $wanted.ContainsKey($name)) { continue }
        if ($result.ContainsKey($name)) { throw "Duplicate readelf symbol: $name" }
        $result[$name] = [pscustomobject]@{
            address = [Convert]::ToUInt64($match.Groups[1].Value, 16)
            size = [UInt64]$match.Groups[2].Value
            bind = $match.Groups[3].Value
            visibility = $match.Groups[4].Value
            section_index = $match.Groups[5].Value
        }
    }
    return $result
}

function Get-NmObjects([string]$Text, [string[]]$Names) {
    $wanted = @{}
    foreach ($name in $Names) { $wanted[$name] = $true }
    $result = @{}
    foreach ($line in $Text -split "`r?`n") {
        $match = [regex]::Match(
            $line,
            '^(\S+)\s+([A-Za-z])\s+([0-9A-Fa-f]+)\s+([0-9A-Fa-f]+)\s*$'
        )
        if (-not $match.Success) { continue }
        $name = $match.Groups[1].Value
        if (-not $wanted.ContainsKey($name)) { continue }
        if ($result.ContainsKey($name)) { throw "Duplicate nm symbol: $name" }
        $result[$name] = [pscustomobject]@{
            address = [Convert]::ToUInt64($match.Groups[3].Value, 16)
            size = [Convert]::ToUInt64($match.Groups[4].Value, 16)
            type = $match.Groups[2].Value
        }
    }
    return $result
}

function Get-DwarfStructSizes([string]$Text, [string[]]$Names) {
    $result = @{}
    foreach ($name in $Names) { $result[$name] = [Collections.Generic.List[UInt64]]::new() }
    $blocks = [regex]::Split(
        $Text,
        '(?m)(?=^\s*<\d+><[0-9A-Fa-f]+>:\s+Abbrev Number:)'
    )
    foreach ($block in $blocks) {
        if ($block -notmatch '\(DW_TAG_structure_type\)') { continue }
        foreach ($name in $Names) {
            $escaped = [regex]::Escape($name)
            if ($block -notmatch "(?m)DW_AT_name\s*:[^`r`n]*\b$escaped\s*$") {
                continue
            }
            $sizeMatch = [regex]::Match(
                $block,
                'DW_AT_byte_size\s*:\s*(?:\([^)]*\)\s*)?(0x[0-9A-Fa-f]+|\d+)'
            )
            # A C forward declaration is emitted as an incomplete DWARF
            # structure DIE without DW_AT_byte_size.  Ignore it and retain the
            # later complete definition.
            if (-not $sizeMatch.Success) { continue }
            $token = $sizeMatch.Groups[1].Value
            $size = if ($token.StartsWith('0x')) {
                [Convert]::ToUInt64($token.Substring(2), 16)
            } else {
                [UInt64]$token
            }
            $result[$name].Add($size)
        }
    }
    return $result
}

try {
    if (Test-Path -LiteralPath $failurePath) {
        Remove-Item -LiteralPath $failurePath -Force
    }
    foreach ($obsoleteKernelEvidence in @(
        (Join-Path $rawDir 'kernel.version.txt'),
        (Join-Path $rawDir 'kernel.version.txt.stderr')
    )) {
        if (Test-Path -LiteralPath $obsoleteKernelEvidence) {
            Remove-Item -LiteralPath $obsoleteKernelEvidence -Force
        }
    }

    $projectRootWsl = ConvertTo-WslPath $projectRoot
    $proofSchedulerWsl = ConvertTo-WslPath (Join-Path $projectRoot 'proof_port\scheduler')
    $proofPortWsl = ConvertTo-WslPath (Join-Path $projectRoot 'proof_port')
    $upstreamIncludeWsl = ConvertTo-WslPath (
        Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include'
    )
    $upstreamSourceWsl = ConvertTo-WslPath (
        Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source'
    )
    $translationUnitWsl = ConvertTo-WslPath $translationUnit
    $linkStubsWsl = ConvertTo-WslPath $linkStubs
    $linkerScriptWsl = ConvertTo-WslPath $linkerScript
    $translationObjectWsl = ConvertTo-WslPath $translationObject
    $stubsObjectWsl = ConvertTo-WslPath $stubsObject
    $elfWsl = ConvertTo-WslPath $elfPath
    $reproElfWsl = ConvertTo-WslPath $reproElfPath
    $mapWsl = ConvertTo-WslPath $mapPath
    $reproMapWsl = ConvertTo-WslPath $reproMapPath

    $compileFlags = @(
        '-m32', '-std=c99', '-O0', '-g3', '-gdwarf-4',
        '-ffreestanding', '-fno-builtin', '-fno-pic', '-fno-pie',
        '-fno-lto', '-fno-common', '-fno-stack-protector',
        '-fno-asynchronous-unwind-tables', '-fno-unwind-tables',
        '-fno-ident', '-fno-eliminate-unused-debug-types',
        '-ffunction-sections', '-fdata-sections',
        '-frandom-seed=eal6-frozen-p2-layout',
        "-fdebug-prefix-map=$projectRootWsl=/workspace/freertos_v611_scheduler",
        "-ffile-prefix-map=$projectRootWsl=/workspace/freertos_v611_scheduler",
        "-fmacro-prefix-map=$projectRootWsl=/workspace/freertos_v611_scheduler",
        '-Wall', '-Wextra', '-Werror', '-fno-strict-aliasing'
    )
    $includeFlags = @(
        '-iquote', $proofSchedulerWsl,
        '-I', $proofSchedulerWsl,
        '-I', $proofPortWsl,
        '-I', $upstreamIncludeWsl,
        '-I', $upstreamSourceWsl
    )
    $linkFlags = @(
        '-m', 'elf_i386', '--build-id=sha1', '--fatal-warnings',
        '--unresolved-symbols=report-all', '-T', $linkerScriptWsl
    )

    Invoke-BoundedWsl 'compile-translation-unit' '/usr/bin/gcc' (
        $compileFlags + $includeFlags + @('-c', $translationUnitWsl, '-o', $translationObjectWsl)
    ) (Join-Path $rawDir 'compile_tu.stdout.txt') (Join-Path $rawDir 'compile_tu.stderr.txt') | Out-Null

    Invoke-BoundedWsl 'compile-link-stubs' '/usr/bin/gcc' (
        $compileFlags + $includeFlags + @('-c', $linkStubsWsl, '-o', $stubsObjectWsl)
    ) (Join-Path $rawDir 'compile_stubs.stdout.txt') (Join-Path $rawDir 'compile_stubs.stderr.txt') | Out-Null

    Invoke-BoundedWsl 'link-primary' '/usr/bin/ld' (
        $linkFlags + @("-Map=$mapWsl", '-o', $elfWsl, $translationObjectWsl, $stubsObjectWsl)
    ) (Join-Path $rawDir 'link.stdout.txt') (Join-Path $rawDir 'link.stderr.txt') | Out-Null

    Invoke-BoundedWsl 'link-reproducibility-copy' '/usr/bin/ld' (
        $linkFlags + @("-Map=$reproMapWsl", '-o', $reproElfWsl, $translationObjectWsl, $stubsObjectWsl)
    ) (Join-Path $rawDir 'link_repro.stdout.txt') (Join-Path $rawDir 'link_repro.stderr.txt') | Out-Null

    $extractCommands = @(
        @('elf-header', '/usr/bin/readelf', @('-hW', $elfWsl), 'elf_header.txt'),
        @('program-headers', '/usr/bin/readelf', @('-lW', $elfWsl), 'program_headers.txt'),
        @('section-headers', '/usr/bin/readelf', @('-SW', $elfWsl), 'section_headers.txt'),
        @('dynamic-section', '/usr/bin/readelf', @('-dW', $elfWsl), 'dynamic_section.txt'),
        @('readelf-symbols', '/usr/bin/readelf', @('-sW', $elfWsl), 'symbols.readelf.txt'),
        @('nm-symbols', '/usr/bin/nm', @('--format=posix', '--print-size', '--radix=x', '--defined-only', $elfWsl), 'symbols.nm.txt'),
        @('objdump-symbols', '/usr/bin/objdump', @('-t', $elfWsl), 'symbols.objdump.txt'),
        @('dwarf-info', '/usr/bin/readelf', @('--debug-dump=info', '--wide', $elfWsl), 'dwarf_info.txt'),
        @('file-identification', '/usr/bin/file', @('-L', $elfWsl), 'file.txt')
    )
    foreach ($spec in $extractCommands) {
        Invoke-BoundedWsl $spec[0] $spec[1] $spec[2] (
            Join-Path $rawDir $spec[3]
        ) (Join-Path $rawDir ($spec[3] + '.stderr')) | Out-Null
    }

    $versionCommands = @(
        @('gcc-version', '/usr/bin/gcc', @('--version'), 'gcc.version.txt'),
        @('gcc-target', '/usr/bin/gcc', @('-dumpmachine'), 'gcc.target.txt'),
        @('assembler-version', '/usr/bin/as', @('--version'), 'as.version.txt'),
        @('linker-version', '/usr/bin/ld', @('--version'), 'ld.version.txt'),
        @('readelf-version', '/usr/bin/readelf', @('--version'), 'readelf.version.txt'),
        @('nm-version', '/usr/bin/nm', @('--version'), 'nm.version.txt'),
        @('objdump-version', '/usr/bin/objdump', @('--version'), 'objdump.version.txt'),
        @('file-version', '/usr/bin/file', @('--version'), 'file.version.txt'),
        @('os-release', '/usr/bin/cat', @('/etc/os-release'), 'os_release.txt'),
        @('gcc-multilib', '/usr/bin/gcc', @('-print-multi-lib'), 'gcc.multilib.txt'),
        @('tool-hashes', '/usr/bin/sha256sum', @('/usr/bin/gcc', '/usr/bin/as', '/usr/bin/ld', '/usr/bin/readelf', '/usr/bin/nm', '/usr/bin/objdump', '/usr/bin/file'), 'tool_hashes.txt')
    )
    foreach ($spec in $versionCommands) {
        Invoke-BoundedWsl $spec[0] $spec[1] $spec[2] (
            Join-Path $rawDir $spec[3]
        ) (Join-Path $rawDir ($spec[3] + '.stderr')) | Out-Null
    }

    $headerText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'elf_header.txt')
    $programText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'program_headers.txt')
    $sectionText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'section_headers.txt')
    $dynamicText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'dynamic_section.txt')
    $readelfText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'symbols.readelf.txt')
    $nmText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'symbols.nm.txt')
    $dwarfText = Get-Content -Raw -LiteralPath (Join-Path $rawDir 'dwarf_info.txt')
    $fileText = (Get-Content -Raw -LiteralPath (Join-Path $rawDir 'file.txt')).Trim()
    $mapText = Get-Content -Raw -LiteralPath $mapPath

    if ($headerText -notmatch 'Class:\s+ELF32') { throw 'ELF class is not ELF32' }
    if ($headerText -notmatch "Data:\s+2's complement, little endian") { throw 'ELF is not little endian' }
    if ($headerText -notmatch 'Type:\s+EXEC') { throw 'ELF is not ET_EXEC/non-PIE' }
    if ($headerText -notmatch 'Machine:\s+Intel 80386') { throw 'ELF machine is not i386' }
    if ($programText -match '\bINTERP\b') { throw 'ELF unexpectedly has a program interpreter' }
    if ($sectionText -notmatch '\.symtab') { throw 'ELF has no static symbol table' }
    foreach ($debugSection in @('.debug_info', '.debug_abbrev', '.debug_line')) {
        if ($sectionText -notmatch [regex]::Escape($debugSection)) {
            throw "ELF is missing $debugSection"
        }
    }
    if ($dynamicText -notmatch 'There is no dynamic section') {
        throw 'ELF unexpectedly has a dynamic section'
    }
    if ($fileText -notmatch 'ELF 32-bit' -or $fileText -notmatch 'not stripped') {
        throw "file(1) did not identify an unstripped ELF32: $fileText"
    }

    $expectedBases = [ordered]@{
        pxReadyTasksLists = [UInt64]80
        xDelayedTaskList1 = [UInt64]20
        xDelayedTaskList2 = [UInt64]20
        xPendingReadyList = [UInt64]20
        xSuspendedTaskList = [UInt64]20
        xTasksWaitingTermination = [UInt64]20
    }
    $baseNames = [string[]]$expectedBases.Keys
    $readelfObjects = Get-ReadelfObjects $readelfText $baseNames
    $nmObjects = Get-NmObjects $nmText $baseNames
    $baseLedger = [Collections.Generic.List[object]]::new()
    foreach ($name in $baseNames) {
        if (-not $readelfObjects.ContainsKey($name)) { throw "readelf did not find $name" }
        if (-not $nmObjects.ContainsKey($name)) { throw "nm did not find $name" }
        $left = $readelfObjects[$name]
        $right = $nmObjects[$name]
        if ($left.address -ne $right.address -or $left.size -ne $right.size) {
            throw "readelf/nm mismatch for $name"
        }
        if ($left.size -ne $expectedBases[$name]) {
            throw "$name has size $($left.size), expected $($expectedBases[$name])"
        }
        if ($left.bind -ne 'LOCAL') { throw "$name is not a local static symbol" }
        if ($right.type -cnotin @('b', 'B')) { throw "$name is not in BSS according to nm" }
        if (($left.address % 4) -ne 0) { throw "$name is not 4-byte aligned" }
        if (($left.address + $left.size) -gt 0x100000000L) { throw "$name wraps 32-bit address space" }
        if ($mapText -notmatch "\b$([regex]::Escape($name))\b") {
            throw "GNU ld map does not mention $name"
        }
        $baseLedger.Add([ordered]@{
            symbol = $name
            address_hex = ('0x{0:x8}' -f $left.address)
            address_decimal = $left.address
            size = $left.size
            readelf_address_hex = ('0x{0:x8}' -f $left.address)
            readelf_size = $left.size
            nm_address_hex = ('0x{0:x8}' -f $right.address)
            nm_size = $right.size
            expected_size = $expectedBases[$name]
            bind = $left.bind
            nm_type = $right.type
            readelf_nm_match = $true
            map_present = $true
        })
    }

    for ($i = 0; $i -lt $baseLedger.Count; ++$i) {
        for ($j = $i + 1; $j -lt $baseLedger.Count; ++$j) {
            $a0 = [UInt64]$baseLedger[$i].address_decimal
            $a1 = $a0 + [UInt64]$baseLedger[$i].size
            $b0 = [UInt64]$baseLedger[$j].address_decimal
            $b1 = $b0 + [UInt64]$baseLedger[$j].size
            if ($a0 -lt $b1 -and $b0 -lt $a1) {
                throw "Base objects overlap: $($baseLedger[$i].symbol), $($baseLedger[$j].symbol)"
            }
        }
    }

    $rootSpecs = @(
        @('ready[0]', 'pxReadyTasksLists', 0),
        @('ready[1]', 'pxReadyTasksLists', 20),
        @('ready[2]', 'pxReadyTasksLists', 40),
        @('ready[3]', 'pxReadyTasksLists', 60),
        @('delayed-A', 'xDelayedTaskList1', 0),
        @('delayed-B', 'xDelayedTaskList2', 0),
        @('pending-ready', 'xPendingReadyList', 0),
        @('suspended', 'xSuspendedTaskList', 0)
    )
    $rootLedger = [Collections.Generic.List[object]]::new()
    foreach ($spec in $rootSpecs) {
        $logicalName = [string]$spec[0]
        $baseName = [string]$spec[1]
        $offset = [UInt64]$spec[2]
        $readelfAddress = [UInt64]$readelfObjects[$baseName].address + $offset
        $nmAddress = [UInt64]$nmObjects[$baseName].address + $offset
        if ($readelfAddress -ne $nmAddress) { throw "Root extraction mismatch for $logicalName" }
        $rootLedger.Add([ordered]@{
            logical_name = $logicalName
            base_symbol = $baseName
            offset = $offset
            address_hex = ('0x{0:x8}' -f $readelfAddress)
            address_decimal = $readelfAddress
            size = [UInt64]20
            readelf_address_hex = ('0x{0:x8}' -f $readelfAddress)
            readelf_size = [UInt64]20
            nm_address_hex = ('0x{0:x8}' -f $nmAddress)
            nm_size = [UInt64]20
            readelf_nm_match = $true
        })
    }
    for ($i = 1; $i -lt 4; ++$i) {
        if (($rootLedger[$i].address_decimal - $rootLedger[$i - 1].address_decimal) -ne 20) {
            throw 'Ready-root stride is not 20 bytes'
        }
    }
    for ($i = 0; $i -lt $rootLedger.Count; ++$i) {
        for ($j = $i + 1; $j -lt $rootLedger.Count; ++$j) {
            $a0 = [UInt64]$rootLedger[$i].address_decimal
            $a1 = $a0 + 20
            $b0 = [UInt64]$rootLedger[$j].address_decimal
            $b1 = $b0 + 20
            if ($a0 -lt $b1 -and $b0 -lt $a1) {
                throw "Physical roots overlap: $($rootLedger[$i].logical_name), $($rootLedger[$j].logical_name)"
            }
        }
    }

    $dwarfExpected = [ordered]@{
        xLIST = [UInt64]20
        xLIST_ITEM = [UInt64]20
        xMINI_LIST_ITEM = [UInt64]12
        tskTaskControlBlock = [UInt64]68
    }
    $dwarfSizes = Get-DwarfStructSizes $dwarfText ([string[]]$dwarfExpected.Keys)
    $dwarfLedger = [Collections.Generic.List[object]]::new()
    foreach ($name in $dwarfExpected.Keys) {
        $sizes = @($dwarfSizes[$name] | Sort-Object -Unique)
        if ($sizes.Count -eq 0) { throw "DWARF does not contain structure $name" }
        if ($dwarfExpected[$name] -notin $sizes) {
            throw "DWARF structure $name sizes $($sizes -join ',') do not include $($dwarfExpected[$name])"
        }
        $dwarfLedger.Add([ordered]@{
            structure = $name
            observed_sizes = [UInt64[]]$sizes
            expected_size = $dwarfExpected[$name]
            expected_present = $true
        })
    }

    $tcbObjectSymbols = @()
    foreach ($line in $readelfText -split "`r?`n") {
        $match = [regex]::Match(
            $line,
            '^\s*\d+:\s+[0-9A-Fa-f]+\s+68\s+OBJECT\s+\S+\s+\S+\s+\S+\s+(\S+)\s*$'
        )
        if ($match.Success) { $tcbObjectSymbols += $match.Groups[1].Value }
    }
    if ($tcbObjectSymbols.Count -ne 0) {
        throw "Unexpected 68-byte ELF object(s); TCBs must remain runtime witnesses: $($tcbObjectSymbols -join ', ')"
    }

    $elfHash = Get-Sha256 $elfPath
    $reproElfHash = Get-Sha256 $reproElfPath
    if ($elfHash -ne $reproElfHash) {
        throw "Deterministic relink failed: $elfHash != $reproElfHash"
    }

    # All validation above consumes the tools' unmodified output.  Only after
    # validation do we canonicalise host-specific roots in textual evidence;
    # hashes below therefore identify portable evidence rather than this clone.
    $textEvidencePaths = @($mapPath, $reproMapPath) + @(
        Get-ChildItem -LiteralPath $rawDir -File |
            Where-Object { $_.Name -match '(\.txt|\.stderr)$' } |
            ForEach-Object { $_.FullName }
    )
    foreach ($textEvidencePath in $textEvidencePaths) {
        Normalize-TextEvidenceFile $textEvidencePath
    }
    $commandsText = ConvertTo-CanonicalCommandText (
        (($commandRecords -join "`n") + "`n")
    )
    Write-Utf8 $commandsPath $commandsText

    $canonicalCompileFlags = @($compileFlags | ForEach-Object {
        ConvertTo-CanonicalEvidenceText $_
    })
    $canonicalIncludeFlags = @($includeFlags | ForEach-Object {
        ConvertTo-CanonicalEvidenceText $_
    })
    $canonicalLinkFlags = @($linkFlags | ForEach-Object {
        ConvertTo-CanonicalEvidenceText $_
    })

    $inputPaths = @(
        $translationUnit,
        (Join-Path $projectRoot 'proof_port\scheduler\FreeRTOSConfig.h'),
        (Join-Path $projectRoot 'proof_port\scheduler\portmacro.h'),
        (Join-Path $projectRoot 'proof_port\scheduler\scheduler_port_contract.h'),
        (Join-Path $projectRoot 'proof_port\scheduler\scheduler_port_contract.c'),
        (Join-Path $projectRoot 'proof_port\scheduler\stdio.h'),
        (Join-Path $projectRoot 'proof_port\scheduler\string.h'),
        (Join-Path $projectRoot 'proof_port\stddef.h'),
        (Join-Path $projectRoot 'proof_port\stdlib.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\tasks.c'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\list.c'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\FreeRTOS.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\list.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\mpu_wrappers.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\portable.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\projdefs.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\StackMacros.h'),
        (Join-Path $projectRoot 'upstream\FreeRTOSV6.1.1\Source\include\task.h'),
        $linkStubs,
        $linkerScript,
        $PSCommandPath
    )
    $inputLedger = @($inputPaths | ForEach-Object {
        [ordered]@{ path = Get-RelativePath $_; sha256 = Get-Sha256 $_ }
    })

    $evidencePaths = @(
        $translationObject, $stubsObject, $elfPath, $reproElfPath,
        $mapPath, $reproMapPath,
        (Join-Path $rawDir 'elf_header.txt'),
        (Join-Path $rawDir 'program_headers.txt'),
        (Join-Path $rawDir 'section_headers.txt'),
        (Join-Path $rawDir 'dynamic_section.txt'),
        (Join-Path $rawDir 'symbols.readelf.txt'),
        (Join-Path $rawDir 'symbols.nm.txt'),
        (Join-Path $rawDir 'symbols.objdump.txt'),
        (Join-Path $rawDir 'dwarf_info.txt'),
        (Join-Path $rawDir 'file.txt'),
        (Join-Path $rawDir 'tool_hashes.txt'),
        $commandsPath
    )
    $evidenceLedger = @($evidencePaths | ForEach-Object {
        [ordered]@{ path = Get-RelativePath $_; sha256 = Get-Sha256 $_ }
    })

    $stopwatch.Stop()
    $toolVersions = [ordered]@{
        gcc = (Get-Content -Raw (Join-Path $rawDir 'gcc.version.txt')).Trim()
        gcc_target = (Get-Content -Raw (Join-Path $rawDir 'gcc.target.txt')).Trim()
        assembler = (Get-Content -Raw (Join-Path $rawDir 'as.version.txt')).Trim()
        linker = (Get-Content -Raw (Join-Path $rawDir 'ld.version.txt')).Trim()
        readelf = (Get-Content -Raw (Join-Path $rawDir 'readelf.version.txt')).Trim()
        nm = (Get-Content -Raw (Join-Path $rawDir 'nm.version.txt')).Trim()
        objdump = (Get-Content -Raw (Join-Path $rawDir 'objdump.version.txt')).Trim()
        file = (Get-Content -Raw (Join-Path $rawDir 'file.version.txt')).Trim()
        os_release = (Get-Content -Raw (Join-Path $rawDir 'os_release.txt')).Trim()
        gcc_multilib = (Get-Content -Raw (Join-Path $rawDir 'gcc.multilib.txt')).Trim()
        executable_sha256 = (Get-Content -Raw (Join-Path $rawDir 'tool_hashes.txt')).Trim()
    }

    $ledger = [ordered]@{
        schema = 1
        status = 'valid'
        source_date_epoch = 0
        project_root = $canonicalProjectRoot
        artifact = [ordered]@{
            path = Get-RelativePath $elfPath
            sha256 = $elfHash
            class = 'ELF32'
            endianness = 'little'
            machine = 'Intel 80386'
            type = 'ET_EXEC'
            pie = $false
            interpreter = $false
            dynamic_section = $false
            stripped = $false
            dwarf = $true
            deterministic_relink_sha256_match = $true
        }
        compile_flags = $canonicalCompileFlags
        include_flags = $canonicalIncludeFlags
        link_flags = $canonicalLinkFlags
        tools = $toolVersions
        base_symbols = $baseLedger
        physical_roots = $rootLedger
        dwarf_structures = $dwarfLedger
        checks = [ordered]@{
            base_symbol_count = $baseLedger.Count
            physical_root_count = $rootLedger.Count
            ready_array_size = 80
            ready_element_size = 20
            ready_stride = 20
            all_base_symbols_readelf_nm_equal = $true
            all_base_symbols_in_link_map = $true
            all_base_regions_pairwise_disjoint = $true
            all_root_regions_pairwise_disjoint = $true
            all_addresses_4_byte_aligned = $true
            all_regions_inside_32_bit_address_space = $true
        }
        tcb_policy = [ordered]@{
            elf_symbols = $false
            detected_68_byte_object_symbols = $tcbObjectSymbols
            statement = 'P2_IDLE and P2_RUN TCBs remain runtime logical witness objects; this artifact certifies static scheduler roots only.'
        }
        trust_boundary = @(
            'GNU GCC/assembler/linker correctness is not verified.',
            'GNU readelf and nm are independent extraction paths but share the Binutils implementation.',
            'This ledger does not connect opaque CParser addressed-data constants to these numeric ELF addresses.',
            'Allocator behaviour, task construction, boot reachability, and deployed-port equivalence remain outside this artifact.'
        )
        inputs = $inputLedger
        evidence = $evidenceLedger
        bounded_processes = $runRecords
    }
    Write-Utf8 $ledgerPath (($ledger | ConvertTo-Json -Depth 12) + "`n")

    $reportLines = [Collections.Generic.List[string]]::new()
    $reportLines.Add('Frozen P2 scheduler layout artifact: VALID')
    $reportLines.Add("ELF: $(Get-RelativePath $elfPath)")
    $reportLines.Add("SHA-256: $elfHash")
    $reportLines.Add('Format: ELF32 little-endian i386 ET_EXEC; non-PIE; no interpreter; no dynamic section; unstripped; DWARF present')
    $reportLines.Add("Deterministic relink: PASS ($reproElfHash)")
    $reportLines.Add('')
    $reportLines.Add('Six addressed static base symbols (readelf == nm; GNU ld map present):')
    foreach ($base in $baseLedger) {
        $reportLines.Add(('  {0,-24} {1} size={2}' -f $base.symbol, $base.address_hex, $base.size))
    }
    $reportLines.Add('')
    $reportLines.Add('Eight physical scheduler roots:')
    foreach ($root in $rootLedger) {
        $reportLines.Add(('  {0,-16} {1} size={2} base={3}+{4}' -f $root.logical_name, $root.address_hex, $root.size, $root.base_symbol, $root.offset))
    }
    $reportLines.Add('')
    $reportLines.Add('Ready array: size=80, element size=20, stride=20; all eight 20-byte regions are pairwise disjoint and 4-byte aligned.')
    $reportLines.Add('DWARF sizes: xLIST=20, xLIST_ITEM=20, xMINI_LIST_ITEM=12, tskTaskControlBlock=68.')
    $reportLines.Add('TCB policy: P2_IDLE/P2_RUN are runtime logical witnesses, not ELF symbols.')
    $reportLines.Add('Limit: this does not yet discharge equality between CParser addressed-data constants and ELF symbol addresses, nor boot/allocator reachability.')
    $reportLines.Add('Runtime measurements are intentionally excluded from the content-addressed certificate.')
    Write-Utf8 $reportPath (($reportLines -join "`n") + "`n")

    $hashPaths = $inputPaths + $evidencePaths + @($ledgerPath, $reportPath, $commandsPath)
    $hashLines = @($hashPaths | Sort-Object -Unique | ForEach-Object {
        "$(Get-Sha256 $_)  $(Get-RelativePath $_)"
    })
    Write-Utf8 $hashesPath (($hashLines -join "`n") + "`n")

    Write-Output ($reportLines -join "`n")
} catch {
    $stopwatch.Stop()
    $failure = @(
        'Frozen P2 scheduler layout artifact: FAILED',
        "message=$($_.Exception.Message)",
        "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"
    ) -join "`n"
    Write-Utf8 $failurePath ($failure + "`n")
    if ($commandRecords.Count -gt 0) {
        Write-Utf8 $commandsPath (($commandRecords -join "`n") + "`n")
    }
    throw
}
