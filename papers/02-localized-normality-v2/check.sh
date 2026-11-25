#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
paper=papers/02-localized-normality-v2
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
mkdir -p "$build/$paper"
lake env lean -o "$build/$paper/Statements.olean" "$paper/Statements.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/Check.lean"' _ "$build" "$paper"
