#!/bin/bash
#SBATCH --account=pl0414-02
#SBATCH --partition=standard
#SBATCH --job-name=transplant_verify
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --time=00:20:00
#SBATCH --output=/mnt/storage_5/scratch/pl0414-02/transplant_verify.%j.out

# Independent re-verification of EML/Framework/TransplantDepths.lean
# (SI §1.5 #5 — variable-transplant depths). Builds the module via
# lake (with cached oleans for everything else) and prints the four
# headline theorems' #check output for sanity.

set -uo pipefail

export PATH="/mnt/storage_5/scratch/pl0414-02/elan_dl/lean-4.28.0-linux/bin:$PATH"

cd /mnt/storage_5/scratch/pl0414-02/lean_workspace

echo "node: $(hostname)"
echo "started: $(date -u +%FT%TZ)"
echo

echo "==== lake build EML.Framework.TransplantDepths ===="
lake build EML.Framework.TransplantDepths 2>&1 \
  | grep -E 'error|warning|Build completed' \
  | head -20
build_exit=${PIPESTATUS[0]}
echo
echo "build_exit=$build_exit"
echo

echo "==== headline theorems ===="
cat > /tmp/transplant_check.lean <<'LEAN'
import EML.Framework.TransplantDepths

#check @EML.EMLTerm.id4_depth
#check @EML.EMLTerm.id4_eval
#check @EML.EMLTerm.transplant4_depth
#check @EML.EMLTerm.transplant4_eval
#check @EML.EMLTerm.idMulFour_depth
#check @EML.EMLTerm.idMulFour_eval
#check @EML.EMLTerm.identity_terms_at_depth_multiples_of_four
LEAN
lake env lean /tmp/transplant_check.lean 2>&1 | head -25
echo

echo "==== no-sorry probe ===="
if grep -nE '^[ \t]*(sorry|admit)\b|:=[ \t]*by[ \t]+sorry|:=[ \t]*by[ \t]+admit' \
    EML/Framework/TransplantDepths.lean; then
  echo "FAIL: stray sorry/admit in TransplantDepths.lean"
  exit 1
else
  echo "OK: no sorry/admit at tactic positions"
fi
echo

echo "completed: $(date -u +%FT%TZ)"
