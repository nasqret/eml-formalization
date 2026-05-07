#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=verify_all
#SBATCH --nodes=1
#SBATCH --cpus-per-task=24
#SBATCH --mem=48G
#SBATCH --time=00:30:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/verify_all.%j.out

# Parallel re-verify of every chunk + framework module across 24 cores.

set -uo pipefail

echo "node:    $(hostname)"
echo "started: $(date -u +%FT%TZ)"

LEAN_TMP=$(mktemp -d /tmp/lean.XXXXXX)
cd "$LEAN_TMP"
zstd -dc ~/pl0414-02/scratch/elan_dl/lean4-v4.28.0-linux.tar.zst | tar -xf - --strip-components=1
export PATH="$LEAN_TMP/bin:$PATH"

WORK_TMP=$(mktemp -d /tmp/work.XXXXXX)
cd "$WORK_TMP"
cp -a /mnt/storage_5/scratch/pl0414-02/lean_workspace/. .
tar -xf /mnt/storage_5/scratch/pl0414-02/lake_cache.tar
echo "ready:   $(date -u +%FT%TZ)"

# Parallel verifier
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
  else
    printf "OK   %s\n" "$bn"
  fi
}
export -f verify_one

find EML/Solutions EML/Framework -name '*.lean' -print0 \
  | xargs -0 -n1 -P 24 -I {} bash -c 'verify_one "$@"' _ {}

echo "completed: $(date -u +%FT%TZ)"
