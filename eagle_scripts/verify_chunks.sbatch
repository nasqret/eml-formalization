#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=chunk_verify
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --time=00:30:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/chunk_verify.%j.out

set -uo pipefail

export ELAN_HOME=/mnt/storage_5/scratch/pl0414-02/elan
export PATH="$ELAN_HOME/bin:$ELAN_HOME/toolchains/leanprover--lean4---v4.28.0/bin:$PATH"

cd /mnt/storage_5/scratch/pl0414-02/lean_workspace

echo "node: $(hostname)"
echo "starting parallel verify across 32 cores at $(date -u +%FT%TZ)"

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
  | xargs -0 -n1 -P 32 -I {} bash -c 'verify_one "$@"' _ {}

echo "completed: $(date -u +%FT%TZ)"
