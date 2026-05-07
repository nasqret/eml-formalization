#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=mathlib_build
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=24
#SBATCH --mem=48G
#SBATCH --time=02:00:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/mathlib_build.%j.out

set -euo pipefail

export ELAN_HOME=/mnt/storage_5/scratch/pl0414-02/elan
export PATH="$ELAN_HOME/bin:$ELAN_HOME/toolchains/leanprover--lean4---v4.28.0/bin:$PATH"

echo "node:    $(hostname)"
echo "started: $(date -u +%FT%TZ)"
echo "lean:    $(lean --version)"
echo "lake:    $(lake --version)"

cd /mnt/storage_5/scratch/pl0414-02/lean_workspace

# First-time Mathlib fetch + build. Use cache if available.
lake exe cache get 2>&1 | tail -5 || true
lake build EML.Basic EML.Term EML.Calc 2>&1 | tail -10

# Then build framework
lake build EML.Framework.Builders.All \
           EML.Framework.Compilers.ELToEML \
           EML.Framework.Compilers.F36ToEL 2>&1 | tail -5

echo "done:    $(date -u +%FT%TZ)"
