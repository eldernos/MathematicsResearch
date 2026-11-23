#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build
lake env lean Audit.lean
while IFS= read -r -d '' source; do
  module=${source%.lean}
  lake env leanchecker "${module//\//.}"
done < <(find NormalityChecker -type f -name '*.lean' -print0 | sort -z)
lake env leanchecker NormalityChecker
