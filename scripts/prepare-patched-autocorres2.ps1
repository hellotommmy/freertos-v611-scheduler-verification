param()

$ErrorActionPreference = 'Stop'

$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$upstreamRoot = 'C:\afp25\afp-2026-07-21\thys\AutoCorres2'
$patchPath = Join-Path $projectRoot 'patches\autocorres2-addressed-global-definitions.patch'
$buildRoot = Join-Path $projectRoot 'build'
$targetRoot = Join-Path $buildRoot 'autocorres2-p2-layout'
$stampPath = Join-Path $targetRoot '.p2-layout-patch-stamp'
$expectedCalculateStateSha256 =
    'EA51ECAA01947E53AD38A684B0E97ED360339363A75C6AE16DCFBA7713562898'

foreach ($required in @($upstreamRoot, $patchPath)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw "Required path is missing: $required"
    }
}

$calculateStatePath = Join-Path $upstreamRoot 'c-parser\calculate_state.ML'
$actualCalculateStateSha256 =
    (Get-FileHash -Algorithm SHA256 -LiteralPath $calculateStatePath).Hash
if ($actualCalculateStateSha256 -ne $expectedCalculateStateSha256) {
    throw "Unexpected calculate_state.ML SHA-256: $actualCalculateStateSha256"
}

$patchSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $patchPath).Hash
$stamp = @(
    "upstream_calculate_state_sha256=$actualCalculateStateSha256",
    "patch_sha256=$patchSha256"
) -join "`n"

$patchedRootFile = Join-Path $targetRoot 'ROOT'
$patchedRootReady = $false
if (Test-Path -LiteralPath $patchedRootFile) {
    $patchedRootReady = [bool](Select-String -LiteralPath $patchedRootFile `
        -Quiet -SimpleMatch 'session AutoCorres2_P2_Layout = Simpl +')
}
if ((Test-Path -LiteralPath $stampPath) -and $patchedRootReady -and
    ((Get-Content -Raw -LiteralPath $stampPath).TrimEnd() -eq $stamp)) {
    Write-Output $targetRoot
    exit 0
}

New-Item -ItemType Directory -Force -Path $buildRoot | Out-Null

if (Test-Path -LiteralPath $targetRoot) {
    $resolvedBuildRoot = (Resolve-Path -LiteralPath $buildRoot).Path
    $resolvedTargetRoot = (Resolve-Path -LiteralPath $targetRoot).Path
    $expectedPrefix = $resolvedBuildRoot.TrimEnd('\') + '\'
    if (-not $resolvedTargetRoot.StartsWith(
        $expectedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing to remove target outside the project build directory: $resolvedTargetRoot"
    }
    Remove-Item -LiteralPath $resolvedTargetRoot -Recurse -Force
}

Copy-Item -LiteralPath $upstreamRoot -Destination $targetRoot -Recurse

$targetRelative = [IO.Path]::GetRelativePath($projectRoot, $targetRoot).Replace('\', '/')

& git -C $projectRoot apply --no-index --unidiff-zero --recount `
    --directory=$targetRelative --check --ignore-space-change $patchPath
if ($LASTEXITCODE -ne 0) {
    throw "AutoCorres2 patch preflight failed with exit code $LASTEXITCODE"
}

& git -C $projectRoot apply --no-index --unidiff-zero --recount `
    --directory=$targetRelative --ignore-space-change $patchPath
if ($LASTEXITCODE -ne 0) {
    throw "AutoCorres2 patch failed with exit code $LASTEXITCODE"
}

Set-Content -LiteralPath $stampPath -Encoding utf8NoBOM -NoNewline -Value $stamp
Write-Output $targetRoot
