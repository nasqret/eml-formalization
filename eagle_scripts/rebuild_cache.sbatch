#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=rebuild_cache
#SBATCH --nodes=1
#SBATCH --cpus-per-task=24
#SBATCH --mem=48G
#SBATCH --time=01:30:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/rebuild_cache.%j.out

echo "node: $(hostname)"
echo "started: $(date)"

LEAN_TMP=$(mktemp -d /tmp/lean.XXXXXX)
cd $LEAN_TMP
zstd -dc ~/pl0414-02/scratch/elan_dl/lean4-v4.28.0-linux.tar.zst | tar -xf - --strip-components=1
export PATH=$LEAN_TMP/bin:$PATH

WORK_TMP=$(mktemp -d /tmp/work.XXXXXX)
cd $WORK_TMP
cp -a /mnt/storage_5/scratch/pl0414-02/lean_workspace/. .

# Restore the existing cache to avoid rebuilding Mathlib from scratch
if [ -f /mnt/storage_5/scratch/pl0414-02/lake_cache.tar ]; then
  echo "extracting existing cache..."
  tar -xf /mnt/storage_5/scratch/pl0414-02/lake_cache.tar
  echo "cache restored at $(date)"
fi

echo "building current Framework + Complex + Bridge..."
lake build EML.Framework.Builders.All 2>&1 | tail -3
lake build EML.Framework.Compilers.ELToEML 2>&1 | tail -3
lake build EML.Framework.Compilers.F36ToEL 2>&1 | tail -3
lake build EML.Framework.Complex.Bridge 2>&1 | tail -3
echo "framework build done at $(date)"

# Replace the cache tar
cd $WORK_TMP
echo "tarring at $(date)"
tar -cf /mnt/storage_5/scratch/pl0414-02/lake_cache.tar.new .lake
mv /mnt/storage_5/scratch/pl0414-02/lake_cache.tar.new /mnt/storage_5/scratch/pl0414-02/lake_cache.tar
echo "tar size: $(du -sh /mnt/storage_5/scratch/pl0414-02/lake_cache.tar | cut -f1)"
echo "DONE at $(date)"
