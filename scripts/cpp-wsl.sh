#!/usr/bin/env bash
set -euo pipefail

# AutoCorres2 invokes cpp with Cygwin paths.  Reuse the existing GNU cpp in
# WSL, translating only absolute Cygwin paths and -I paths to /mnt/<drive>/...
# paths.  All other flags are forwarded byte-for-byte.

cygwin_to_wsl_path() {
  local cygwin_path="$1"
  local windows_path
  local drive
  local rest

  windows_path="$(cygpath -aw -- "$cygwin_path")"
  drive="${windows_path:0:1}"
  rest="${windows_path:3}"
  rest="${rest//\\//}"
  printf '/mnt/%s/%s' "${drive,,}" "$rest"
}

converted=()
for argument in "$@"; do
  case "$argument" in
    -I/*)
      converted+=("-I$(cygwin_to_wsl_path "${argument#-I}")")
      ;;
    /*)
      converted+=("$(cygwin_to_wsl_path "$argument")")
      ;;
    *)
      converted+=("$argument")
      ;;
  esac
done

exec /cygdrive/c/Windows/System32/wsl.exe \
  -d Ubuntu \
  --exec /usr/bin/cpp \
  "${converted[@]}"
