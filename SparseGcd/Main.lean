import SparseGcd.Machine.Analysis
import SparseGcd.Machine.Clock
import SparseGcd.Machine.Amplify
import Complexitylib.SAT.CookLevin.Assembly

/-!
# Main theorems (Theorem 18 = Theorem 3, Theorem 19 = Theorem 4)

Both are conditional on the BCR/AIRR prime construction (`PrimeConstruction`, Lemma 14), which
is an external dependency not closed in this development. Everything else is proved.
-/

open Complexity SparseDiv

namespace SparseGcd

/-- `NP ⊆ BPP` from `SAT ∈ BPP` (Cook–Levin + closure of `BPP` under polynomial-time many-one
reductions). -/
theorem NP_subset_BPP_of_SAT_mem_BPP (h : SAT.language ∈ BPP) : NP ⊆ BPP := fun L hL ↦
  SparseDiv.mem_BPP_of_mapReducesBPP (SparseDiv.MapReducesPoly.mapReducesBPP (SAT.NPHard_language L hL))
    (SparseDiv.promiseBPP_ofLanguage_of_mem_BPP h)

/-- **Theorem 18 (= Theorem 3).** An output-sensitive sparse gcd solver gives `SAT ∈ BPP`. -/
theorem SAT_mem_BPP_of_gcdSolver (C : PrimeConstruction) (S : GcdSolver) : SAT.language ∈ BPP :=
  (gcdOracle S).SAT_mem_BPP C

theorem NP_subset_BPP_of_gcdSolver (C : PrimeConstruction) (S : GcdSolver) : NP ⊆ BPP :=
  NP_subset_BPP_of_SAT_mem_BPP (SAT_mem_BPP_of_gcdSolver C S)

/-- Contrapositive: under `NP ⊄ BPP` there is no output-sensitive sparse gcd solver. -/
theorem no_gcdSolver_of_NP_not_subset_BPP (C : PrimeConstruction) (h : ¬ NP ⊆ BPP) : IsEmpty GcdSolver :=
  ⟨fun S ↦ h (NP_subset_BPP_of_gcdSolver C S)⟩

/-- **Theorem 19 (= Theorem 4).** A promise-BPP decider for roots-of-unity detection gives
`SAT ∈ BPP`. -/
theorem SAT_mem_BPP_of_promiseBPP_rou (C : PrimeConstruction) (h : SparseDiv.PromiseBPP rouPromise) :
    SAT.language ∈ BPP := by
  obtain ⟨V, ℓ, hV, hsolve⟩ := SparseDiv.promiseRandomTapeBPP_of_promiseBPP h
  exact (rouOracle V ℓ hV hsolve).SAT_mem_BPP C

theorem NP_subset_BPP_of_promiseBPP_rou (C : PrimeConstruction) (h : SparseDiv.PromiseBPP rouPromise) :
    NP ⊆ BPP :=
  NP_subset_BPP_of_SAT_mem_BPP (SAT_mem_BPP_of_promiseBPP_rou C h)

theorem NP_subset_BPP_of_rou_mem_P (C : PrimeConstruction) (h : RootsOfUnity ∈ P) : NP ⊆ BPP :=
  NP_subset_BPP_of_promiseBPP_rou C (promiseBPP_rouPromise_of_mem_P h)

theorem NP_subset_BPP_of_rou_mem_BPP (C : PrimeConstruction) (h : RootsOfUnity ∈ BPP) : NP ⊆ BPP :=
  NP_subset_BPP_of_promiseBPP_rou C (promiseBPP_rouPromise_of_mem_BPP h)

/-- Contrapositive. -/
theorem rou_not_promiseBPP_of_NP_not_subset_BPP (C : PrimeConstruction) (h : ¬ NP ⊆ BPP) :
    ¬ SparseDiv.PromiseBPP rouPromise :=
  fun hp ↦ h (NP_subset_BPP_of_promiseBPP_rou C hp)

theorem rou_not_mem_P_of_NP_not_subset_BPP (C : PrimeConstruction) (h : ¬ NP ⊆ BPP) :
    RootsOfUnity ∉ P :=
  fun hp ↦ h (NP_subset_BPP_of_rou_mem_P C hp)

end SparseGcd
