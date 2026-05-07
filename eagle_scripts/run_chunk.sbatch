#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=run_chunk
#SBATCH --nodes=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --time=00:30:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/run_chunk.%j.out

# Canonical workhorse: extract toolchain + lake cache to /tmp, then run a
# user-specified command (typically `lake env lean <chunk.lean>`).
#
# Pass the command via env var WORK_CMD when submitting, e.g.:
#   sbatch --export=ALL,WORK_CMD='lake env lean EML/Solutions/061_emlterm_for_artanh_x.lean' run_chunk.sbatch

set -uo pipefail

WORK_CMD="${WORK_CMD:-echo \"WORK_CMD not set\"; exit 1}"

echo "node:    $(hostname)"
echo "started: $(date -u +%FT%TZ)"

# 1. Extract Lean toolchain (~3 sec)
LEAN_TMP=$(mktemp -d /tmp/lean.XXXXXX)
cd "$LEAN_TMP"
zstd -dc ~/pl0414-02/scratch/elan_dl/lean4-v4.28.0-linux.tar.zst | tar -xf - --strip-components=1
export PATH="$LEAN_TMP/bin:$PATH"

# 2. Extract lake_cache (~30 sec): contains .lake with all Mathlib + framework oleans
WORK_TMP=$(mktemp -d /tmp/work.XXXXXX)
cd "$WORK_TMP"
cp -a /mnt/storage_5/scratch/pl0414-02/lean_workspace/. .
tar -xf /mnt/storage_5/scratch/pl0414-02/lake_cache.tar
echo "ready:   $(date -u +%FT%TZ)"

# 3. Run the user command. WORK_CMD runs in WORK_TMP with PATH set up.
echo "==> WORK_CMD: $WORK_CMD"
echo "------------------------------------------------------------"
eval "$WORK_CMD"
RC=$?
echo "------------------------------------------------------------"
echo "rc:      $RC"
echo "done:    $(date -u +%FT%TZ)"

exit $RC
