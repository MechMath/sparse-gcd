#!/usr/bin/env bash
# Audit of the SparseGcd library: build, forbidden-token scan, axioms of the main declarations.
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/.."
lake build 2>&1 | tail -3
echo "--- sorry / admit / axiom / native_decide / unsafe occurrences in SparseGcd/ ---"
grep -rn -E "\b(sorry|admit|native_decide|unsafe|implemented_by|extern)\b|^axiom " SparseGcd || echo "none"
echo "--- axioms of main declarations ---"
mkdir -p scratch
cat > scratch/audit_gcd.lean <<'LEAN'
import SparseGcd
open SparseGcd
-- main theorems (Theorem 18 = Theorem 3, Theorem 19 = Theorem 4, contrapositives)
#check @SAT_mem_BPP_of_gcdSolver
#print axioms SAT_mem_BPP_of_gcdSolver
#check @NP_subset_BPP_of_gcdSolver
#print axioms NP_subset_BPP_of_gcdSolver
#check @no_gcdSolver_of_NP_not_subset_BPP
#print axioms no_gcdSolver_of_NP_not_subset_BPP
#check @SAT_mem_BPP_of_promiseBPP_rou
#print axioms SAT_mem_BPP_of_promiseBPP_rou
#check @NP_subset_BPP_of_promiseBPP_rou
#print axioms NP_subset_BPP_of_promiseBPP_rou
#check @NP_subset_BPP_of_rou_mem_P
#print axioms NP_subset_BPP_of_rou_mem_P
#check @NP_subset_BPP_of_rou_mem_BPP
#print axioms NP_subset_BPP_of_rou_mem_BPP
#check @rou_not_promiseBPP_of_NP_not_subset_BPP
#print axioms rou_not_promiseBPP_of_NP_not_subset_BPP
#check @rou_not_mem_P_of_NP_not_subset_BPP
#print axioms rou_not_mem_P_of_NP_not_subset_BPP
#check @NP_subset_BPP_of_SAT_mem_BPP
#print axioms NP_subset_BPP_of_SAT_mem_BPP
-- hypotheses (structures)
#check @GcdSolver
#check @PrimeConstruction
#check @DegreeOracle
#check @rouPromise
#check @RootsOfUnity
-- shared lemmas
#print axioms eventProb_isolatingSeeds_ge
#print axioms eventProb_isolateSeed_unique_ge
#print axioms isolate_unsat
#print axioms card_solutions_of_windowExt
#print axioms PrimePackage.E_div_p_le
#print axioms card_goodBases_ge
#print axioms totient_div_ge
#print axioms RootData.commonZeros_constraintPolys
#print axioms RootData.existsUnique_coeff
#print axioms RootData.monicGcd_of_success
#print axioms RootData.length_Hterms_le
#print axioms eventProb_bitsVal_mod_le
#print axioms eventProb_compressionFail_le
#print axioms eventProb_findOmega_none_le_tenth
#print axioms clockedSolver_eq
#print axioms gcdOracle
#print axioms rouOracle
#print axioms DegreeOracle.eventProb_trialAccept_le_of_unsat
#print axioms DegreeOracle.eventProb_trialAccept_ge_of_sat
#print axioms DegreeOracle.randomTapeSolves_SAT
#print axioms DegreeOracle.verdictStr_mem_FP
#print axioms DegreeOracle.SAT_mem_BPP
LEAN
lake env lean scratch/audit_gcd.lean 2>&1 | tee docs/AXIOMS.txt
rm -f scratch/audit_gcd.lean
