#!/usr/bin/env bash
# Build the committed LaTeX sources. Keep auxiliary files outside the source tree.
set -euo pipefail
paper_root=$(cd "$(dirname "$0")" && pwd)
build_root=$(mktemp -d)
trap 'rm -rf "$build_root"' EXIT
# TeX Live honors this value for embedded dates; it is the Checkpoint 11 timestamp.
export SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH:-1795547923}
export FORCE_SOURCE_DATE=1
export TZ=UTC

if (($#)); then
  paper_names=("$@")
else
  # Archived v1.1 manuscripts first, then the manuscripts-v2 candidates that exist.
  paper_names=(01-stoneham-polynomials 02-localized-normality 03-signed-resonance
               04-arithmetic-certificates 05-classical-denominators)
  for candidate in 06-multiplicative-lambert 01-stoneham-polynomials-v2 07-synthetic-expansions 10-discrepancy-arithmetic 08-stoneham-product-orbits 02-localized-normality-v2 05-classical-denominators-v2 04-arithmetic-certificates-v2 09-erdos-borwein-note; do
    [[ -f "$paper_root/$candidate/paper.tex" ]] && paper_names+=("$candidate")
  done
fi
for name in "${paper_names[@]}"; do
  dir="$paper_root/$name"
  if [[ ! -f "$dir/paper.tex" ]]; then
    echo "Missing manuscript source: $dir/paper.tex" >&2
    exit 1
  fi
  mkdir -p "$build_root/$name"
  (
    cd "$dir"
    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
      -outdir="$build_root/$name" paper.tex
  )
  log="$build_root/$name/paper.log"
  if grep -Eq 'There were undefined (references|citations)|LaTeX Warning: (Reference|Citation).* undefined' "$log"; then
    echo "Unresolved cross-reference or citation in $name" >&2
    exit 1
  fi
  cp "$build_root/$name/paper.pdf" "$dir/paper.pdf"
done
