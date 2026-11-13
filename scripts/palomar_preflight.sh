#!/usr/bin/env bash
# Mechanical checks before Palomar submission (DomainTheory/scott1980 pattern).
set -euo pipefail
cd "$(dirname "$0")/.."

step() { printf '\n== %s ==\n' "$1"; }

step "Validate Comparator configuration"
python3 - <<'PY'
import json
with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
required = ("challenge_module", "solution_module", "theorem_names",
            "definition_names", "permitted_axioms")
missing = [k for k in required if k not in cfg]
if missing:
    raise SystemExit(f"Missing comparator keys: {', '.join(missing)}")
names = cfg["theorem_names"] + cfg["definition_names"]
dupes = sorted({n for n in names if names.count(n) > 1})
if dupes:
    raise SystemExit(f"Duplicate Comparator names: {', '.join(dupes)}")
print(f"OK: {len(cfg['theorem_names'])} theorem targets and "
      f"{len(cfg['definition_names'])} definition targets.")
PY

step "Build Lean project"
lake build

step "Reject proof holes in Solution / Actions sources"
if rg -n --glob '*.lean' \
    '(^|:=|by)[[:space:]]+sorry([[:space:];]|$)|^[[:space:]]*sorry([[:space:];]|$)' \
    Actions Solution.lean Challenge.lean; then
  echo "FAIL: Lean sources contain sorry."
  exit 1
fi
echo "OK: no sorry in Actions / Challenge / Solution."

step "Batch A compared declarations elaborate"
lake env lean --run /dev/null 2>/dev/null || true
lake build Challenge Solution
echo "OK: Challenge and Solution build."

echo
echo "Preflight complete (Batch A). PALOMAR_URL remains TBD until registry assign."
echo "Batch B (MotCalc / promise CF) blocked on 1973 scans."
