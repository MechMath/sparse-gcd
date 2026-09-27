import SparseDivComplexity.Terms
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Monic greatest common divisors over a field

`IsMonicGcd g f₁ f₂` is the instance-free specification "`g` is monic, divides both, and is
divisible by every common divisor". Monic gcds are unique. `monicGcd f₁ f₂` is the canonical
representative built from `EuclideanDomain.gcd` (with `monicGcd 0 0 = 0`, the only case without a
monic gcd). For `R = ∏_{β ∈ S} (X - C β)` with distinct roots, `gcd(R, H) = ∏_{β ∈ S, H(β)=0} (X - C β)`,
so `deg gcd(R,H) > 0` iff `R` and `H` have a common root in the base field; and
`¬ IsCoprime f₁ f₂ ↔ 0 < deg (monicGcd f₁ f₂)`.

`termsOf q` is the canonical sparse term list of a polynomial over `ZMod p`.
-/

open Polynomial Finset

namespace SparseGcd

variable {K : Type*} [Field K]

/-- `g` is the monic gcd of `f₁` and `f₂`. -/
def IsMonicGcd (g f₁ f₂ : K[X]) : Prop :=
  g.Monic ∧ g ∣ f₁ ∧ g ∣ f₂ ∧ ∀ d : K[X], d ∣ f₁ → d ∣ f₂ → d ∣ g

theorem IsMonicGcd.unique {g g' f₁ f₂ : K[X]} (h : IsMonicGcd g f₁ f₂) (h' : IsMonicGcd g' f₁ f₂) :
    g = g' :=
  eq_of_monic_of_associated h.1 h'.1
    (associated_of_dvd_dvd (h'.2.2.2 g h.2.1 h.2.2.1) (h.2.2.2 g' h'.2.1 h'.2.2.1))

theorem IsMonicGcd.symm {g f₁ f₂ : K[X]} (h : IsMonicGcd g f₁ f₂) : IsMonicGcd g f₂ f₁ :=
  ⟨h.1, h.2.2.1, h.2.1, fun d h₂ h₁ ↦ h.2.2.2 d h₁ h₂⟩

/-- A monic gcd only exists when not both inputs are zero. -/
theorem IsMonicGcd.ne_zero_or_ne_zero {g f₁ f₂ : K[X]} (h : IsMonicGcd g f₁ f₂) :
    f₁ ≠ 0 ∨ f₂ ≠ 0 := by
  by_contra hcon
  simp only [ne_eq, not_or, not_not] at hcon
  obtain ⟨rfl, rfl⟩ := hcon
  exact h.1.ne_zero (zero_dvd_iff.mp (h.2.2.2 0 (dvd_zero _) (dvd_zero _)))

/-- The canonical monic gcd (`0` when both inputs are `0`). -/
noncomputable def monicGcd [DecidableEq K] (f₁ f₂ : K[X]) : K[X] :=
  let g := EuclideanDomain.gcd f₁ f₂
  g * C (g.leadingCoeff)⁻¹

theorem monicGcd_zero_zero [DecidableEq K] : monicGcd (0 : K[X]) 0 = 0 := by
  simp [monicGcd]

theorem isMonicGcd_monicGcd [DecidableEq K] {f₁ f₂ : K[X]} (h : f₁ ≠ 0 ∨ f₂ ≠ 0) :
    IsMonicGcd (monicGcd f₁ f₂) f₁ f₂ := by
  have hg : EuclideanDomain.gcd f₁ f₂ ≠ 0 := by
    rw [Ne, EuclideanDomain.gcd_eq_zero_iff]; tauto
  have hu : IsUnit (C (EuclideanDomain.gcd f₁ f₂).leadingCoeff⁻¹) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hg)).isUnit
  unfold monicGcd
  refine ⟨monic_mul_leadingCoeff_inv hg, ?_, ?_, ?_⟩
  · exact hu.mul_right_dvd.mpr (EuclideanDomain.gcd_dvd_left f₁ f₂)
  · exact hu.mul_right_dvd.mpr (EuclideanDomain.gcd_dvd_right f₁ f₂)
  · intro d h₁ h₂
    exact hu.dvd_mul_right.mpr (EuclideanDomain.dvd_gcd h₁ h₂)

theorem monicGcd_eq_of_isMonicGcd [DecidableEq K] {g f₁ f₂ : K[X]} (h : IsMonicGcd g f₁ f₂) :
    monicGcd f₁ f₂ = g :=
  (isMonicGcd_monicGcd h.ne_zero_or_ne_zero).unique h

theorem monicGcd_comm [DecidableEq K] (f₁ f₂ : K[X]) : monicGcd f₁ f₂ = monicGcd f₂ f₁ := by
  by_cases h : f₁ ≠ 0 ∨ f₂ ≠ 0
  · exact monicGcd_eq_of_isMonicGcd (isMonicGcd_monicGcd h.symm).symm
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem monicGcd_zero_right [DecidableEq K] {f : K[X]} (hf : f.Monic) : monicGcd f 0 = f :=
  monicGcd_eq_of_isMonicGcd ⟨hf, dvd_rfl, dvd_zero _, fun _ h _ ↦ h⟩

theorem monicGcd_dvd_left [DecidableEq K] (f₁ f₂ : K[X]) : monicGcd f₁ f₂ ∣ f₁ := by
  by_cases h : f₁ ≠ 0 ∨ f₂ ≠ 0
  · exact (isMonicGcd_monicGcd h).2.1
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dvd_zero _

theorem monicGcd_dvd_right [DecidableEq K] (f₁ f₂ : K[X]) : monicGcd f₁ f₂ ∣ f₂ := by
  by_cases h : f₁ ≠ 0 ∨ f₂ ≠ 0
  · exact (isMonicGcd_monicGcd h).2.2.1
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dvd_zero _

/-- Non-coprimality is positive gcd degree (when not both zero). -/
theorem not_isCoprime_iff_natDegree_monicGcd_pos [DecidableEq K] {f₁ f₂ : K[X]}
    (h : f₁ ≠ 0 ∨ f₂ ≠ 0) : ¬ IsCoprime f₁ f₂ ↔ 0 < (monicGcd f₁ f₂).natDegree := by
  have hm := (isMonicGcd_monicGcd h).1
  have hg : EuclideanDomain.gcd f₁ f₂ ≠ 0 := by
    rw [Ne, EuclideanDomain.gcd_eq_zero_iff]; tauto
  have hu : IsUnit (C (EuclideanDomain.gcd f₁ f₂).leadingCoeff⁻¹) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hg)).isUnit
  have key : IsUnit (EuclideanDomain.gcd f₁ f₂) ↔ monicGcd f₁ f₂ = 1 := by
    constructor
    · intro h1
      exact hm.eq_one_of_isUnit (h1.mul hu)
    · intro h1
      have h2 : IsUnit (monicGcd f₁ f₂) := h1 ▸ isUnit_one
      exact isUnit_of_dvd_unit (dvd_mul_right _ _) h2
  rw [Nat.pos_iff_ne_zero, Ne, hm.natDegree_eq_zero, ← key, EuclideanDomain.gcd_isUnit_iff]

/-- The gcd of a product of distinct linear factors with `H` is the product over the common roots. -/
theorem isMonicGcd_prod_filter [DecidableEq K] (S : Finset K) (H : K[X]) :
    IsMonicGcd (∏ β ∈ S.filter fun β ↦ H.eval β = 0, (X - C β)) (∏ β ∈ S, (X - C β)) H := by
  have hRm : (∏ β ∈ S, (X - C β)).Monic := monic_prod_of_monic _ _ fun β _ ↦ monic_X_sub_C β
  refine ⟨monic_prod_of_monic _ _ fun β _ ↦ monic_X_sub_C β,
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _), ?_, ?_⟩
  · refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
    · intro β hβ
      rw [dvd_iff_isRoot]
      exact (Finset.mem_filter.mp hβ).2
  · intro D hD₁ hD₂
    have hD0 : D ≠ 0 := by
      rintro rfl
      exact hRm.ne_zero (zero_dvd_iff.mp hD₁)
    have hsplit : D.Splits :=
      (Splits.prod fun β _ ↦ Splits.X_sub_C β).of_dvd hRm.ne_zero hD₁
    refine hsplit.dvd_of_roots_le_roots hD0 ?_
    have hle : D.roots ≤ S.val := by
      rw [← roots_prod_X_sub_C]
      exact roots.le_of_dvd hRm.ne_zero hD₁
    rw [roots_prod_X_sub_C, Multiset.le_iff_subset (Multiset.nodup_of_le hle S.nodup)]
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter]
    exact ⟨Finset.mem_val.mp (Multiset.subset_of_le hle hx),
      eval_eq_zero_of_dvd_of_eval_eq_zero hD₂ ((mem_roots hD0).mp hx)⟩

theorem monicGcd_prod_filter [DecidableEq K] (S : Finset K) (H : K[X]) :
    monicGcd (∏ β ∈ S, (X - C β)) H = ∏ β ∈ S.filter fun β ↦ H.eval β = 0, (X - C β) :=
  monicGcd_eq_of_isMonicGcd (isMonicGcd_prod_filter S H)

/-- `deg gcd(R, H) > 0` iff a root of `R` is a root of `H` (for `R` a product of distinct linear
factors). -/
theorem natDegree_monicGcd_prod_pos_iff [DecidableEq K] (S : Finset K) (H : K[X]) :
    0 < (monicGcd (∏ β ∈ S, (X - C β)) H).natDegree ↔ ∃ β ∈ S, H.eval β = 0 := by
  rw [monicGcd_prod_filter, natDegree_prod_of_monic _ _ fun β _ ↦ monic_X_sub_C β]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_pos,
    Finset.filter_nonempty_iff]

theorem monicGcd_prod_eq_one_iff [DecidableEq K] (S : Finset K) (H : K[X]) :
    monicGcd (∏ β ∈ S, (X - C β)) H = 1 ↔ ∀ β ∈ S, H.eval β ≠ 0 := by
  have hm : (monicGcd (∏ β ∈ S, (X - C β)) H).Monic := by
    rw [monicGcd_prod_filter]; exact monic_prod_of_monic _ _ fun β _ ↦ monic_X_sub_C β
  rw [← hm.natDegree_eq_zero]
  constructor
  · intro h0 β hβ hβ0
    have := (natDegree_monicGcd_prod_pos_iff S H).mpr ⟨β, hβ, hβ0⟩
    omega
  · intro h
    by_contra h0
    obtain ⟨β, hβ, hβ0⟩ := (natDegree_monicGcd_prod_pos_iff S H).mp (Nat.pos_of_ne_zero h0)
    exact h β hβ hβ0

theorem monicGcd_prod_eq_X_sub_C [DecidableEq K] (S : Finset K) (H : K[X]) {α : K}
    (h : S.filter (fun β ↦ H.eval β = 0) = {α}) :
    monicGcd (∏ β ∈ S, (X - C β)) H = X - C α := by
  rw [monicGcd_prod_filter, h, Finset.prod_singleton]

/-- `X^n - 1 = ∏_{β ∈ nthRootsFinset n 1} (X - C β)` when a primitive `n`-th root exists. -/
theorem X_pow_sub_one_eq_prod_nthRoots {ζ : K} {n : ℕ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (X ^ n - 1 : K[X]) = ∏ β ∈ nthRootsFinset n (1 : K), (X - C β) :=
  Polynomial.X_pow_sub_one_eq_prod hn hζ

/-! ### Canonical term lists of polynomials over `ZMod p` -/

/-- The canonical sparse term list of a polynomial: exponents in increasing order, residues. -/
noncomputable def termsOf (p : ℕ) [NeZero p] (q : (ZMod p)[X]) : SparseDiv.Terms :=
  (q.support.sort (· ≤ ·)).map fun e ↦ ((q.coeff e).val, e)

theorem toPoly_termsOf (p : ℕ) [NeZero p] (q : (ZMod p)[X]) : SparseDiv.toPoly p (termsOf p q) = q := by
  conv_rhs => rw [as_sum_support q]
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq q.support (· ≤ ·), Multiset.map_coe,
    Multiset.sum_coe]
  simp only [termsOf, SparseDiv.toPoly, List.map_map, Function.comp_def, ZMod.natCast_zmod_val,
    C_mul_X_pow_eq_monomial]

theorem normalized_termsOf (p : ℕ) [NeZero p] (q : (ZMod p)[X]) :
    SparseDiv.Normalized p (termsOf p q) := by
  refine ⟨?_, ?_⟩
  · rw [termsOf, List.pairwise_map]
    exact (Finset.sortedLT_sort q.support).pairwise
  · intro t ht
    rw [termsOf, List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    rw [Finset.mem_sort, mem_support_iff] at he
    exact ⟨ZMod.val_pos.mpr he, ZMod.val_lt _⟩

theorem length_termsOf (p : ℕ) [NeZero p] (q : (ZMod p)[X]) :
    (termsOf p q).length = q.support.card := by
  rw [termsOf, List.length_map, Finset.length_sort]

theorem termsOf_toPoly_of_normalized {p : ℕ} [NeZero p] {l : SparseDiv.Terms}
    (h : SparseDiv.Normalized p l) : termsOf p (SparseDiv.toPoly p l) = l := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  calc termsOf p (SparseDiv.toPoly p l)
      = SparseDiv.normalize p (termsOf p (SparseDiv.toPoly p l)) :=
        (SparseDiv.normalize_of_normalized hp (normalized_termsOf p _)).symm
    _ = SparseDiv.normalize p l := SparseDiv.normalize_eq_of_toPoly_eq hp (toPoly_termsOf p _)
    _ = l := SparseDiv.normalize_of_normalized hp h

theorem termsOf_zero (p : ℕ) [NeZero p] : termsOf p (0 : (ZMod p)[X]) = [] := by
  simp [termsOf]

theorem termsOf_one (p : ℕ) [NeZero p] (hp : 1 < p) : termsOf p (1 : (ZMod p)[X]) = [(1, 0)] := by
  have h1 : SparseDiv.toPoly p [(1, 0)] = 1 := by simp [SparseDiv.toPoly]
  rw [← h1]
  exact termsOf_toPoly_of_normalized ⟨List.pairwise_singleton _ _, by simp [hp]⟩

theorem termsOf_X_sub_C (p : ℕ) [NeZero p] (hp : 1 < p) {α : ZMod p} (hα : α ≠ 0) :
    termsOf p (X - C α) = [((-α).val, 0), (1, 1)] := by
  have h1 : SparseDiv.toPoly p [((-α).val, 0), (1, 1)] = X - C α := by
    simp only [SparseDiv.toPoly_cons, SparseDiv.toPoly_nil, ZMod.natCast_zmod_val, Nat.cast_one,
      C_neg, C_1, pow_zero, pow_one, mul_one, one_mul, add_zero]
    ring
  rw [← h1]
  refine termsOf_toPoly_of_normalized ⟨?_, ?_⟩
  · simp
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨ZMod.val_pos.mpr (neg_ne_zero.mpr hα), ZMod.val_lt _⟩
    · exact ⟨Nat.one_pos, hp⟩

end SparseGcd
