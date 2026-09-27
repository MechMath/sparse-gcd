import SparseGcd.Cnf.Basic
import Complexitylib.Classes.Randomized.Hashing.Affine
import Complexitylib.Classes.EventProb
import Mathlib.Data.Nat.Size

/-!
# Valiant–Vazirani isolation (Lemma 12)

For a nonempty `S ⊆ {0,1}^m` and `k ≥ 1` with `2^{k-2} ≤ |S| ≤ 2^{k-1}`, a seed of the affine
pairwise-independent family `{0,1}^m → {0,1}^k` (complexitylib's `PairwiseIndependentHash.affine`,
which includes an explicit offset column) isolates exactly one element of `S` in the target cell
`0` with probability at least `1/8`.

The proof only uses the `uniform` and `pairwise` fields: for `x ∈ S`,
`Pr[h x = 0 ∧ ∀ y ∈ S ∖ {x}, h y ≠ 0] ≥ 2^{-k} - (|S|-1) 2^{-2k} ≥ 2^{-k-1}`, and these events are
disjoint over `x ∈ S`, so the total is at least `|S| 2^{-k-1} ≥ 1/8`.
-/

open Complexity Finset

namespace SparseGcd

/-- The target cell: all-zero output. -/
def zeroCell (k : ℕ) : BitString k := fun _ ↦ false

/-- Seeds isolating exactly one element of `S` in the zero cell. -/
def isolatingSeeds {m k : ℕ} (S : Finset (BitString m)) :
    Finset (BitString (PairwiseIndependentHash.affineSeedWidth m k)) :=
  univ.filter fun seed ↦
    (S.filter fun x ↦ PairwiseIndependentHash.affineEval seed x = zeroCell k).card = 1

/-- The arithmetic core of the isolation bound: with `n = |S|` and `P = 2^k`,
`n (1/P - (n-1)/P²) ≥ 1/8` whenever `P/4 ≤ n ≤ P/2`. -/
private theorem isolation_arith (n P : ℚ) (hn : 1 ≤ n) (hlow : P ≤ 4 * n) (hhigh : 2 * n ≤ P) :
    (1 : ℚ) / 8 ≤ n * (1 / P - (n - 1) / P ^ 2) := by
  have hP : 0 < P := by linarith
  have hP0 : P ≠ 0 := hP.ne'
  have key : n * (1 / P - (n - 1) / P ^ 2) - 1 / 8 =
      (8 * n * P - 8 * n * (n - 1) - P ^ 2) / (8 * P ^ 2) := by
    field_simp
  have hnum : 0 ≤ 8 * n * P - 8 * n * (n - 1) - P ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hhigh) (sub_nonneg.2 hlow),
      mul_pos (by linarith : (0 : ℚ) < n) hP]
  have := div_nonneg hnum (by positivity : (0 : ℚ) ≤ 8 * P ^ 2)
  linarith

/-- Generic isolation lemma for any pairwise-independent family. -/
theorem eventProb_isolating_ge_of_pairwise {m k w : ℕ}
    (hash : PairwiseIndependentHash m k w) (S : Finset (BitString m))
    (hS : S.Nonempty) (hlow : 2 ^ k ≤ 4 * S.card) (hhigh : 2 * S.card ≤ 2 ^ k) :
    (1 : ℚ) / 8 ≤ eventProb (univ.filter fun seed : BitString w ↦
      (S.filter fun x ↦ hash.eval seed x = zeroCell k).card = 1) := by
  classical
  have hn : 0 < S.card := card_pos.2 hS
  -- the event "`x` is alone in the zero cell"
  let A : BitString m → Finset (BitString w) := fun x ↦ univ.filter fun seed ↦
    hash.eval seed x = zeroCell k ∧ ∀ y ∈ S, y ≠ x → hash.eval seed y ≠ zeroCell k
  have hAx : ∀ x ∈ S, 1 / (2 : ℚ) ^ k - (S.card - 1) / 2 ^ (2 * k) ≤ eventProb (A x) := by
    intro x hx
    let C : BitString m → Finset (BitString w) := fun y ↦ univ.filter fun seed ↦
      hash.eval seed x = zeroCell k ∧ hash.eval seed y = zeroCell k
    have hsub : (univ.filter fun seed : BitString w ↦ hash.eval seed x = zeroCell k) ⊆
        A x ∪ (S.erase x).biUnion C := by
      intro seed hseed
      rw [mem_filter] at hseed
      by_cases h : ∀ y ∈ S, y ≠ x → hash.eval seed y ≠ zeroCell k
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hseed.2, h⟩)
      · push Not at h
        obtain ⟨y, hyS, hyx, hy⟩ := h
        exact mem_union_right _ (mem_biUnion.2 ⟨y, mem_erase.2 ⟨hyx, hyS⟩,
          mem_filter.2 ⟨mem_univ _, hseed.2, hy⟩⟩)
    have h1 := eventProb_mono hsub
    have h2 := eventProb_union_le (A x) ((S.erase x).biUnion C)
    have h3 := eventProb_biUnion_le (S.erase x) C
    rw [hash.uniform x (zeroCell k)] at h1
    have h4 : ∑ y ∈ S.erase x, eventProb (C y) = (S.card - 1) / 2 ^ (2 * k) := by
      rw [sum_congr rfl fun y hy ↦
          hash.pairwise (Ne.symm (mem_erase.1 hy).1) (zeroCell k) (zeroCell k),
        sum_const, card_erase_of_mem hx, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ S.card)]
      push_cast
      ring
    linarith
  have hdisj : (S : Set (BitString m)).PairwiseDisjoint A := by
    intro x hx y hy hxy
    rw [Function.onFun, disjoint_left]
    intro seed hsx hsy
    rw [mem_filter] at hsx hsy
    exact hsx.2.2 y hy (Ne.symm hxy) hsy.2.1
  have hsub : S.biUnion A ⊆ univ.filter fun seed : BitString w ↦
      (S.filter fun x ↦ hash.eval seed x = zeroCell k).card = 1 := by
    intro seed hseed
    obtain ⟨x, hx, hseed⟩ := mem_biUnion.1 hseed
    rw [mem_filter] at hseed
    refine mem_filter.2 ⟨mem_univ _, card_eq_one.2 ⟨x, ?_⟩⟩
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hy, hy0⟩
      by_contra hyx
      exact hseed.2.2 y hy hyx hy0
    · rintro rfl
      exact ⟨hx, hseed.2.1⟩
  have hn' : (1 : ℚ) ≤ S.card := by exact_mod_cast hn
  have hlow' : (2 : ℚ) ^ k ≤ 4 * S.card := by exact_mod_cast hlow
  have hhigh' : 2 * (S.card : ℚ) ≤ 2 ^ k := by exact_mod_cast hhigh
  calc (1 : ℚ) / 8 ≤ S.card * (1 / 2 ^ k - (S.card - 1) / (2 ^ k) ^ 2) :=
        isolation_arith _ _ hn' hlow' hhigh'
    _ = ∑ x ∈ S, (1 / (2 : ℚ) ^ k - (S.card - 1) / 2 ^ (2 * k)) := by
        rw [sum_const, nsmul_eq_mul, pow_mul']
    _ ≤ ∑ x ∈ S, eventProb (A x) := sum_le_sum hAx
    _ = eventProb (S.biUnion A) := (eventProb_biUnion S A hdisj).symm
    _ ≤ _ := eventProb_mono hsub

/-- **Lemma 12 (Valiant–Vazirani) for the affine family.** -/
theorem eventProb_isolatingSeeds_ge {m k : ℕ} (S : Finset (BitString m))
    (hS : S.Nonempty) (hlow : 2 ^ k ≤ 4 * S.card) (hhigh : 2 * S.card ≤ 2 ^ k) :
    (1 : ℚ) / 8 ≤ eventProb (isolatingSeeds (k := k) S) :=
  eventProb_isolating_ge_of_pairwise (PairwiseIndependentHash.affine m k) S hS hlow hhigh

/-- A suitable `k` always exists: `k = Nat.size |S| + 1`. -/
theorem exists_k_of_card {m : ℕ} (S : Finset (BitString m)) (hS : S.Nonempty) :
    2 ^ (Nat.size S.card + 1) ≤ 4 * S.card ∧ 2 * S.card ≤ 2 ^ (Nat.size S.card + 1) ∧
      Nat.size S.card + 1 ≤ m + 2 := by
  have hn : 0 < S.card := card_pos.2 hS
  have h1 : S.card < 2 ^ Nat.size S.card := Nat.lt_size_self _
  have hs : 0 < Nat.size S.card := Nat.size_pos.2 hn
  have h2 : 2 ^ (Nat.size S.card - 1) ≤ S.card := Nat.lt_size.1 (by omega)
  have h3 : S.card ≤ 2 ^ m := by
    have := card_le_univ S
    rwa [card_finArrowBool] at this
  have h4 : Nat.size S.card ≤ m + 1 := by
    rw [Nat.size_le, pow_succ]
    have : 0 < 2 ^ m := by positivity
    omega
  refine ⟨?_, ?_, by omega⟩
  · have : 2 ^ (Nat.size S.card + 1) = 4 * 2 ^ (Nat.size S.card - 1) := by
      rw [show Nat.size S.card + 1 = (Nat.size S.card - 1) + 2 by omega, pow_add]
      ring
    omega
  · rw [pow_succ]
    omega

/-- The parity constraint read off row `i` of an affine seed: the selected variables and the target
bit (the offset column is the last coordinate of the augmented input). -/
def rowVars {m k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k)) (i : Fin k) :
    List ℕ :=
  (List.finRange m).filterMap fun j ↦
    if PairwiseIndependentHash.affineRows seed i (Fin.castSucc j) then some j.val else none

def rowTarget {m k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k)) (i : Fin k) :
    Bool :=
  PairwiseIndependentHash.affineRows seed i (Fin.last m)

/-- Parity of the row's selected variables under `g`. -/
def rowParity (g : ℕ → Bool) (xs : List ℕ) : Bool := xs.foldl (fun b x ↦ xor b (g x)) false

/-- Folding `xor` over the selected variables of a list computes the Boolean-ring sum
`∑ A j * x j` (up to the initial accumulator). -/
private theorem foldl_parity_filterMap {m : ℕ} (A : Fin m → Bool) (x : BitString m) :
    ∀ (l : List (Fin m)) (b : Bool),
      ((l.filterMap fun j ↦ if A j then some j.val else none).foldl
          (fun b v ↦ xor b (toFun x v)) b) = xor b (l.map fun j ↦ A j * x j).sum
  | [], b => by simp [Bool.zero_eq_false]
  | j :: l, b => by
    have hj : toFun x j.val = x j := by simp [toFun]
    rw [List.map_cons, List.sum_cons, Bool.add_eq_xor, Bool.mul_eq_and]
    by_cases h : A j = true
    · rw [List.filterMap_cons_some (b := j.val) (by simp [h]), List.foldl_cons,
        foldl_parity_filterMap A x l, hj, h, Bool.true_and, Bool.xor_assoc]
    · have h' : A j = false := by simpa using h
      rw [List.filterMap_cons_none (by simp [h']), foldl_parity_filterMap A x l, h',
        Bool.false_and, Bool.false_xor]

private theorem xor_eq_false_iff (a b : Bool) : (a ^^ b) = false ↔ a = b := by
  cases a <;> cases b <;> decide

/-- The linear part of row `i` is the parity of the selected variables. -/
private theorem sum_castSucc_eq_rowParity {m k : ℕ}
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k)) (x : BitString m) (i : Fin k) :
    ∑ j : Fin m, PairwiseIndependentHash.affineRows seed i j.castSucc * x j =
      rowParity (toFun x) (rowVars seed i) := by
  rw [rowParity, rowVars,
    foldl_parity_filterMap (fun j ↦ PairwiseIndependentHash.affineRows seed i j.castSucc) x,
    Bool.false_xor, ← List.ofFn_eq_map, List.sum_ofFn]

/-- Row `i` of the affine hash is zero on `x` iff the parity of the selected variables equals the
target bit. -/
theorem affineEval_row_eq_false_iff {m k : ℕ}
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k)) (x : BitString m) (i : Fin k) :
    PairwiseIndependentHash.affineEval seed x i = false ↔
      rowParity (toFun x) (rowVars seed i) = rowTarget seed i := by
  show (∑ column, PairwiseIndependentHash.affineRows seed i column *
      PairwiseIndependentHash.affineAugment x column) = false ↔ _
  rw [Fin.sum_univ_castSucc]
  simp only [PairwiseIndependentHash.affineAugment_castSucc_internal,
    PairwiseIndependentHash.affineAugment_last_internal]
  rw [sum_castSucc_eq_rowParity, rowTarget, Bool.mul_eq_and, Bool.and_true, Bool.add_eq_xor]
  exact xor_eq_false_iff _ _

theorem affineEval_eq_zeroCell_iff {m k : ℕ}
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k)) (x : BitString m) :
    PairwiseIndependentHash.affineEval seed x = zeroCell k ↔
      ∀ i : Fin k, rowParity (toFun x) (rowVars seed i) = rowTarget seed i := by
  rw [funext_iff]
  exact forall_congr' fun i ↦ affineEval_row_eq_false_iff seed x i

theorem rowVars_lt {m k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k))
    (i : Fin k) : ∀ x ∈ rowVars seed i, x < m := by
  intro v hv
  simp only [rowVars, List.mem_filterMap, List.mem_finRange, true_and] at hv
  obtain ⟨j, hj⟩ := hv
  split_ifs at hj
  rw [← Option.some.inj hj]
  exact j.isLt

theorem rowVars_length_le {m k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m k))
    (i : Fin k) : (rowVars seed i).length ≤ m :=
  calc (rowVars seed i).length ≤ (List.finRange m).length := List.length_filterMap_le _ _
    _ = m := List.length_finRange

end SparseGcd
