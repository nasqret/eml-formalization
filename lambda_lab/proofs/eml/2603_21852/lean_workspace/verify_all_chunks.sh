#!/usr/bin/env bash
# ============================================================================
# Verify all 62 EML chunk solutions in parallel.
#
# Usage:
#   ./verify_all_chunks.sh                # auto-detect cores
#   ./verify_all_chunks.sh 32             # explicit core count
#
# Output: one line per chunk (OK/FAIL). On FAIL, prints first 3 error lines.
# Exit code: 0 if all OK, 1 if any failure.
#
# This is the speed lever: on a 32-core box, all 62 chunks verify in ~30s
# instead of the ~10 min sequential time on a laptop. Especially useful
# for re-verifying after Tier 1 / Tier 2 batch edits.
# ============================================================================

set -uo pipefail

cd "$(dirname "$0")"

CORES="${1:-$(sysctl -n hw.logicalcpu 2>/dev/null || nproc 2>/dev/null || echo 4)}"
LOG=/tmp/eml_verify_$$.log
START=$(date +%s)

echo "verifying 62 chunks across $CORES cores..."

verify_one() {
  local f="$1"
  local bn=$(basename "$f")
  local out
  out=$(lake env lean "$f" 2>&1)
  local errs
  errs=$(echo "$out" | grep -cE '^[^:]+\.lean:[0-9]+:[0-9]+: error:' || true)
  if [ "$errs" -gt 0 ]; then
    printf "FAIL %s\n" "$bn"
    echo "$out" | grep -E "error" | head -3
    return 1
  else
    printf "OK   %s\n" "$bn"
    return 0
  fi
}
export -f verify_one

# xargs -P CORES runs CORES jobs concurrently. -I {} substitutes each filename.
find EML/Solutions -name '*.lean' -print0 \
  | xargs -0 -n1 -P "$CORES" -I {} bash -c 'verify_one "$@"' _ {} \
  > "$LOG" 2>&1

ELAPSED=$(( $(date +%s) - START ))
TOTAL=$(wc -l < "$LOG")
FAILS=$(grep -c '^FAIL' "$LOG" || echo 0)
OKS=$(grep -c '^OK' "$LOG" || echo 0)

echo
echo "=========================================="
echo "verified $TOTAL chunks in ${ELAPSED}s"
echo "  OK:   $OKS"
echo "  FAIL: $FAILS"
echo "=========================================="

if [ "$FAILS" -gt 0 ]; then
  echo
  echo "FAILURES:"
  grep -E "^FAIL|error:" "$LOG"
  exit 1
fi
