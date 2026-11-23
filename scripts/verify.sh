#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build
lake env lean Audit.lean
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
