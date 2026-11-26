#!/usr/bin/env bash
# Build manuscripts with the WSL TinyTeX toolchain. From the repository root on Windows:
#   wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert
export PATH="$HOME/bin:$PATH"
exec bash "$(cd "$(dirname "$0")" && pwd)/build.sh" "$@"
