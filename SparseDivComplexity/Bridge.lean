import Mathlib

/-
SparseDiv.Bridge: the **Divisibility Bridge** lemma.

This module is the Lean 4 formalization of Lemma 4 (`lem:bridge`, "The
Divisibility Bridge") from the paper *Sparse Polynomial Divisibility Test is
CoNP-hard* (`paper.tex`, Section "Non-divisibility test over finite fields is
NP-hard"). The bridge turns the question "does the sparse polynomial `P` have a
root in `𝔽_p`?" into a single sparse divisibility test `g_P ∣ f_P`, which is the
engine of the NP-hardness reduction for the non-divisibility test.

## The construction

Let `p` be prime and `P ∈ 𝔽_p[X]`. Define a pair of polynomials:

* if `P ≠ 0`:  `f_P = P(Xᵖ) - P(X)`  and  `g_P = (Xᵖ - X) · P(X)`;
* if `P = 0`:  `f_P = 1`            and  `g_P = X`  (the *guarded* pair, so that
  `g_P` is always a well-formed nonzero divisor).

Here `𝔽_p` is modelled by `ZMod p` together with `[Fact p.Prime]`, and "`P` has
a root in `𝔽_p`" is rendered as `∃ a : ZMod p, P.eval a = 0`.

## Contents

The bridge statement is split into the following named results, mirroring the
clauses of the paper lemma.

* `SparseDiv.fP`, `SparseDiv.gP` — the construction `P ↦ (f_P, g_P)`.
* `SparseDiv.gP_ne_zero`        — `g_P ≠ 0` (the divisor is well-formed).
* `SparseDiv.gP_dvd_fP_iff`     — the **bridge equivalence**:
  `g_P ∣ f_P ↔ P` has no root in `𝔽_p`.
* `SparseDiv.gP_not_dvd_fP_iff` — its contrapositive (the form actually used by
  the reduction): `g_P ∤ f_P ↔ P` has a root in `𝔽_p`.
* `SparseDiv.natDegree_fP_le`   — degree bound `deg f_P ≤ p · deg P` (for `P ≠ 0`).
* `SparseDiv.natDegree_gP_le`   — degree bound `deg g_P ≤ p + deg P` (for `P ≠ 0`).

Two reusable ingredients of the proof are also exposed as standalone lemmas:

* `SparseDiv.comp_X_pow_eq_pow`  — Frobenius in characteristic `p`:
  `P(Xᵖ) = P(X)ᵖ` (the displayed identity `P(x^p) = P(x)^p` in the proof).
* `SparseDiv.dvd_X_pow_sub_X_iff` — the divisibility criterion `(2)` of the
  proof: `(Xᵖ - X) ∣ R ↔ R` vanishes on all of `𝔽_p`.

## Scope

The degree bounds `natDegree_fP_le` / `natDegree_gP_le` formalize the displayed
inequalities `deg f_P ≤ pE`, `deg g_P ≤ p + E`. The lemma's remaining
"`≤ 2t` terms" / "polynomial sparse bit-size blowup" clauses are informal
bit-complexity statements and are not formalized here.

The development is checked with Lean `4.29.0` and mathlib `v4.29.0`, and is
free of `sorry`.
-/

open Polynomial

namespace SparseDiv

variable {p : ℕ} [Fact p.Prime]

/-- The polynomial `f_P` of the bridge lemma (`lem:bridge`): the dividend
`P(Xᵖ) - P(X)` when `P ≠ 0`, and the guarded value `1` when `P = 0`. -/
noncomputable def fP (P : (ZMod p)[X]) : (ZMod p)[X] :=
  if P = 0 then 1 else P.comp (X ^ p) - P

/-- The polynomial `g_P` of the bridge lemma (`lem:bridge`): the divisor
`(Xᵖ - X) · P(X)` when `P ≠ 0`, and the guarded value `X` when `P = 0`. -/
noncomputable def gP (P : (ZMod p)[X]) : (ZMod p)[X] :=
  if P = 0 then X else (X ^ p - X) * P

/-- Guarded case: `f_0 = 1`. -/
@[simp] theorem fP_zero : fP (0 : (ZMod p)[X]) = 1 := by simp [fP]

/-- Guarded case: `g_0 = X`. -/
@[simp] theorem gP_zero : gP (0 : (ZMod p)[X]) = X := by simp [gP]

/-- Unfolding of `f_P` in the main (nonzero) case. -/
theorem fP_of_ne_zero {P : (ZMod p)[X]} (hP : P ≠ 0) :
    fP P = P.comp (X ^ p) - P := by simp [fP, hP]

/-- Unfolding of `g_P` in the main (nonzero) case. -/
theorem gP_of_ne_zero {P : (ZMod p)[X]} (hP : P ≠ 0) :
    gP P = (X ^ p - X) * P := by simp [gP, hP]

/-- **Frobenius in characteristic `p`.**  Over `𝔽_p` we have `P(Xᵖ) = P(X)ᵖ`,
because every coefficient `c ∈ 𝔽_p` satisfies `cᵖ = c`.

This is the displayed identity `P(x^p) = P(x)^p` used in the proof of
`lem:bridge`. It is proved by recognizing `P.comp (Xᵖ)` as `Polynomial.expand`
and applying `ZMod.expand_card`. -/
theorem comp_X_pow_eq_pow (P : (ZMod p)[X]) : P.comp (X ^ p) = P ^ p := by
  rw [← expand_eq_comp_X_pow, ZMod.expand_card]

/-- **Divisibility criterion for `Xᵖ - X`** — equation `(2)` in the proof of
`lem:bridge`. For any `R ∈ 𝔽_p[X]`, `(Xᵖ - X) ∣ R` iff `R` vanishes at every
point of `𝔽_p`.

The forward direction is evaluation (using `aᵖ = a` on `𝔽_p`). The backward
direction divides `R` by the monic `Xᵖ - X`: the remainder `B` again vanishes
everywhere but has degree `< p`, hence is `0` (a nonzero polynomial of degree
`< p` cannot have all `p` field elements as roots). -/
theorem dvd_X_pow_sub_X_iff (R : (ZMod p)[X]) :
    (X ^ p - X) ∣ R ↔ ∀ a : ZMod p, R.eval a = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- `Xᵖ - X` vanishes everywhere on `𝔽_p` (Fermat's little theorem).
  have hAeval : ∀ a : ZMod p, (X ^ p - X : (ZMod p)[X]).eval a = 0 := by
    intro a; simp [eval_sub, eval_pow, eval_X, ZMod.pow_card]
  constructor
  · -- Forward direction: evaluate.
    rintro ⟨Q, rfl⟩ a
    simp [eval_mul, hAeval a]
  · -- Backward direction: Euclidean division by the monic `Xᵖ - X`.
    intro h
    have hAmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
      apply monic_X_pow_sub
      rw [degree_X]; exact_mod_cast hp1
    have hAnd : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp1
    have hA0 : (X ^ p - X : (ZMod p)[X]) ≠ 0 := hAmonic.ne_zero
    -- The remainder `B = R %ₘ (Xᵖ - X)` also vanishes everywhere.
    have hBeval : ∀ a : ZMod p, (R %ₘ (X ^ p - X)).eval a = 0 := by
      intro a
      have hsum := congrArg (Polynomial.eval a) (modByMonic_add_div R (X ^ p - X))
      rw [eval_add, eval_mul, hAeval a, zero_mul, add_zero] at hsum
      rw [hsum]; exact h a
    -- ... but `deg B < p`, so `B = 0` (a nonzero poly of degree `< p`
    -- cannot vanish at all `p` points).
    have hBnd : (R %ₘ (X ^ p - X)).natDegree < p := by
      by_cases hB0 : R %ₘ (X ^ p - X) = 0
      · rw [hB0, natDegree_zero]; exact (Fact.out : p.Prime).pos
      · have hdlt := degree_modByMonic_lt R hAmonic
        rw [degree_eq_natDegree hA0, hAnd] at hdlt
        exact (natDegree_lt_iff_degree_lt hB0).mpr hdlt
    haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
    have hBzero : R %ₘ (X ^ p - X) = 0 :=
      eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := (id : ZMod p → ZMod p))
        Function.injective_id hBeval (by rw [ZMod.card]; exact hBnd)
    -- Hence `Xᵖ - X` divides `R`.
    refine ⟨R /ₘ (X ^ p - X), ?_⟩
    have hsum := modByMonic_add_div R (X ^ p - X)
    rw [hBzero, zero_add] at hsum
    exact hsum.symm

/-- **`g_P ≠ 0`** (first clause of `lem:bridge`): the divisor is always a
well-formed nonzero polynomial. In the main case `g_P = (Xᵖ - X)·P` is a product
of nonzeros in the integral domain `𝔽_p[X]`; in the guarded case `g_P = X ≠ 0`. -/
theorem gP_ne_zero (P : (ZMod p)[X]) : gP P ≠ 0 := by
  by_cases hP : P = 0
  · subst hP; simp
  · rw [gP_of_ne_zero hP]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hA0 : (X ^ p - X : (ZMod p)[X]) ≠ 0 := by
      have hd : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
        FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp1
      intro h; rw [h, natDegree_zero] at hd; omega
    exact mul_ne_zero hA0 hP

/-- **The bridge equivalence** (central clause of `lem:bridge`): `g_P ∣ f_P`
holds exactly when `P` has *no* root in `𝔽_p`.

In the main case the proof factors `f_P = Pᵖ - P = (P^{p-1} - 1)·P` via
Frobenius, cancels the common factor `P` (`𝔽_p[X]` is a domain), reducing to
`(Xᵖ - X) ∣ P^{p-1} - 1` (equation `(1)`); the criterion `dvd_X_pow_sub_X_iff`
then turns this into the vanishing of `P^{p-1} - 1` on `𝔽_p`, which by Fermat's
little theorem says precisely that `P` has no root. The guarded case `P = 0` is
immediate: `X ∤ 1`, while `0` has every element of `𝔽_p` as a root. -/
theorem gP_dvd_fP_iff (P : (ZMod p)[X]) :
    gP P ∣ fP P ↔ ¬ ∃ a : ZMod p, P.eval a = 0 := by
  by_cases hP : P = 0
  · -- Guarded case: `g_P = X`, `f_P = 1`; `X ∤ 1`, and `0` is a root of `0`.
    subst hP
    rw [fP_zero, gP_zero]
    constructor
    · intro hdvd
      exact absurd (natDegree_le_of_dvd hdvd one_ne_zero) (by simp [natDegree_X])
    · intro hnr
      exact absurd ⟨(0 : ZMod p), by simp⟩ hnr
  · -- Main case `P ≠ 0`.
    rw [fP_of_ne_zero hP, gP_of_ne_zero hP, comp_X_pow_eq_pow P]
    -- `f_P = Pᵖ - P = (P^{p-1} - 1)·P`.
    rw [show P ^ p - P = (P ^ (p - 1) - 1) * P from by
      rw [sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]]
    -- Cancel the common factor `P` (valid since `𝔽_p[X]` is a domain).
    rw [mul_dvd_mul_iff_right hP, dvd_X_pow_sub_X_iff]
    simp only [eval_sub, eval_pow, eval_one]
    constructor
    · -- If `P^{p-1} - 1` vanishes everywhere, `P` has no root.
      intro h hex
      obtain ⟨a, ha⟩ := hex
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have := h a
      rw [ha, zero_pow (by omega : p - 1 ≠ 0)] at this
      simp at this
    · -- If `P` has no root, then for every `a`, `P(a)^{p-1} = 1`.
      intro hnr a
      have hane : P.eval a ≠ 0 := fun hh => hnr ⟨a, hh⟩
      rw [ZMod.pow_card_sub_one_eq_one hane, sub_self]

/-- **The bridge equivalence, root form** (the "equivalently" clause of
`lem:bridge`): `g_P ∤ f_P` exactly when `P` has a root in `𝔽_p`. This is the
contrapositive form consumed by the NP-hardness reduction, where deciding
non-divisibility decides root existence. -/
theorem gP_not_dvd_fP_iff (P : (ZMod p)[X]) :
    ¬ gP P ∣ fP P ↔ ∃ a : ZMod p, P.eval a = 0 := by
  rw [gP_dvd_fP_iff, not_not]

/-- **Degree bound** `deg f_P ≤ p · deg P` for `P ≠ 0` (the displayed
`deg f_P ≤ pE` of `lem:bridge`, with `E = deg P`). -/
theorem natDegree_fP_le {P : (ZMod p)[X]} (hP : P ≠ 0) :
    (fP P).natDegree ≤ p * P.natDegree := by
  rw [fP_of_ne_zero hP]
  have h1 : (P.comp (X ^ p)).natDegree = p * P.natDegree := by
    rw [natDegree_comp, natDegree_X_pow, Nat.mul_comm]
  have h2 := natDegree_sub_le (P.comp (X ^ p)) P
  rw [h1] at h2
  refine h2.trans (max_le le_rfl ?_)
  exact le_mul_of_one_le_left (Nat.zero_le _) (Fact.out : p.Prime).one_lt.le

/-- **Degree bound** `deg g_P ≤ p + deg P` for `P ≠ 0` (the displayed
`deg g_P ≤ p + E` of `lem:bridge`, with `E = deg P`). -/
theorem natDegree_gP_le {P : (ZMod p)[X]} (hP : P ≠ 0) :
    (gP P).natDegree ≤ p + P.natDegree := by
  rw [gP_of_ne_zero hP]
  refine natDegree_mul_le.trans ?_
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) (Fact.out : p.Prime).one_lt]

end SparseDiv
