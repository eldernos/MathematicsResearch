#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -B -m unittest discover -s scripts -p 'test_*.py'
lake build
lake env lean Audit.lean
for paper in papers/[0-9][0-9]-*/; do
  if [[ -x "${paper}check.sh" ]]; then
    "${paper}check.sh"
  elif [[ -f "${paper}Check.lean" ]]; then
    lake env lean "${paper}Check.lean"
  elif [[ -f "${paper}check.lean" ]]; then
    lake env lean "${paper}check.lean"
  fi
done
NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean
# Registry, links, anchors, result identifiers, topics, generated pages and figures.
python3 -B scripts/portal.py check --strict
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
