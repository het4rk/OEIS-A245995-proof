#!/usr/bin/env bash
# Usage: check_axioms.sh <file with `lake env lean Axioms.lean` output>
# Fails on errors, sorryAx, or any axiom outside propext / Classical.choice / Quot.sound.
set -euo pipefail
f="$1"
if grep -qiE "error|sorry" "$f"; then echo "FAIL: error or sorry in axiom report"; cat "$f"; exit 1; fi
n=$(grep -c "depends on axioms" "$f" || true)
if [ "$n" -eq 0 ]; then echo "FAIL: no axiom lines found"; exit 1; fi
bad=$(grep "depends on axioms" "$f" | sed -E 's/.*\[(.*)\].*/\1/' | tr ',' '\n' | sed 's/ //g' \
      | grep -vxE "propext|Classical.choice|Quot.sound" || true)
if [ -n "$bad" ]; then echo "FAIL: non-standard axioms: $bad"; exit 1; fi
echo "OK: $n declarations, axioms within [propext, Classical.choice, Quot.sound]"
