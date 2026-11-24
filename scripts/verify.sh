#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -B -m unittest discover -s scripts -p 'test_*.py'
lake build
lake env lean Audit.lean
lake env lean papers/01-stoneham-polynomials/check.lean
papers/02-localized-normality/check.sh
NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean
while IFS= read -r -d '' source; do
  module=${source%.lean}
  echo "Replaying ${module//\//.}"
  lake env leanchecker "${module//\//.}"
done < <(find NormalityChecker -type f -name '*.lean' -print0 | sort -z)
# The CLI treats a module name as a prefix. Replay the root alone after its children.
echo "Replaying NormalityChecker"
lake env lean --stdin <<'LEAN'
import LeanChecker
#eval replayFromImports `NormalityChecker
LEAN
