import SparseDivComplexity.Terms

/-!
# The divisibility bridge on sparse term lists

The paper's Lemma 4 (`lem:bridge`) is stated for sparse polynomials. `SparseDivComplexity.Bridge`
(the original `EonMath/sparse-div` development) formalizes the algebra on `(ZMod p)[X]`; this module
implements the construction on *term lists* exactly as the paper describes it:

* for `P = ∑ cᵢ X^{eᵢ} ≠ 0`: `f_P` has the terms `(cᵢ, p·eᵢ)` and `(-cᵢ, eᵢ)`, and `g_P` has the
  terms `(cᵢ, p + eᵢ)` and `(-cᵢ, eᵢ + 1)`, after which like terms are collected and zero
  coefficients deleted;
* for `P = 0`: the guarded pair `f_P = 1`, `g_P = X`.

## Main definitions

* `SparseDiv.negMod p c` — the canonical representative of `-c` modulo `p`.
* `SparseDiv.fTermsRaw`, `SparseDiv.gTermsRaw` — the displayed (uncollected) term lists.
* `SparseDiv.bridgeTerms p l` — the full algorithm (zero test, generation, collection).
* `SparseDiv.targetDegreeBound p D = 1 + max (p·D) (max (p + D) 1)` — the paper's `D′`.

## Main results

* `toPoly_bridgeTerms_fst`, `toPoly_bridgeTerms_snd` — the algorithm computes `fP`, `gP`.
* `card_support_fP_le`, `card_support_gP_le` — at most `2 t` terms after collection (`P ≠ 0`);
  `card_support_fP_zero`, `card_support_gP_zero` — one term each in the guarded case.
* `length_bridgeTerms_fst_le`, `length_bridgeTerms_snd_le` — the same bound on the output lists.
* `natDegree_fP_lt_targetDegreeBound`, `natDegree_gP_lt_targetDegreeBound`,
  `size_targetDegreeBound_le` — the degree bound `D′` and its bit length `O(log p + log (D + 1))`.
-/

open Polynomial

namespace SparseDiv

/-- The canonical representative in `[0, p)` of `-c` modulo `p`. -/
def negMod (p c : ℕ) : ℕ := (p - c % p) % p

theorem natCast_negMod {p : ℕ} (hp : 0 < p) (c : ℕ) :
    ((negMod p c : ℕ) : ZMod p) = -((c : ℕ) : ZMod p) := by
  unfold negMod
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hp).le, ZMod.natCast_self, ZMod.natCast_mod,
    zero_sub]

theorem negMod_lt {p : ℕ} (hp : 0 < p) (c : ℕ) : negMod p c < p := Nat.mod_lt _ hp

@[simp] theorem negMod_zero (p : ℕ) : negMod p 0 = 0 := by
  simp [negMod]

/-- The displayed terms of `f_P = P(X^p) - P(X)`: `(cᵢ, p·eᵢ)` followed by `(-cᵢ, eᵢ)`. -/
def fTermsRaw (p : ℕ) (l : Terms) : Terms :=
  (l.map fun t ↦ (t.1, p * t.2)) ++ l.map fun t ↦ (negMod p t.1, t.2)

/-- The displayed terms of `g_P = (X^p - X)·P(X)`: `(cᵢ, p + eᵢ)` followed by `(-cᵢ, eᵢ + 1)`. -/
def gTermsRaw (p : ℕ) (l : Terms) : Terms :=
  (l.map fun t ↦ (t.1, p + t.2)) ++ l.map fun t ↦ (negMod p t.1, t.2 + 1)

/-- The guarded outputs for `P = 0`: `f_0 = 1` and `g_0 = X`. -/
def guardedTerms : Terms × Terms := ([(1, 0)], [(1, 1)])

/-- **The bridge algorithm on term lists.** Normalize the input; if it is empty output the guarded
pair, otherwise generate the displayed terms of `f_P` and `g_P` and collect like terms. -/
def bridgeTerms (p : ℕ) (l : Terms) : Terms × Terms :=
  let n := normalize p l
  if n = [] then guardedTerms else (normalize p (fTermsRaw p n), normalize p (gTermsRaw p n))

@[simp] theorem length_fTermsRaw (p : ℕ) (l : Terms) : (fTermsRaw p l).length = 2 * l.length := by
  simp [fTermsRaw]; omega

@[simp] theorem length_gTermsRaw (p : ℕ) (l : Terms) : (gTermsRaw p l).length = 2 * l.length := by
  simp [gTermsRaw]; omega

/-- The terms `(cᵢ, p·eᵢ)` denote `P(X^p)`. -/
private theorem toPoly_map_mul_exp (p : ℕ) (l : Terms) :
    toPoly p (l.map fun t ↦ (t.1, p * t.2)) = (toPoly p l).comp (X ^ p) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPoly_cons, add_comp, C_mul_comp, X_pow_comp, ih, pow_mul]

/-- The terms `(cᵢ, k + eᵢ)` denote `X^k · P`. -/
private theorem toPoly_map_add_exp (p k : ℕ) (l : Terms) :
    toPoly p (l.map fun t ↦ (t.1, k + t.2)) = X ^ k * toPoly p l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPoly_cons, ih, pow_add]; ring

/-- The terms `(-cᵢ, eᵢ)` denote `-P`. -/
private theorem toPoly_map_negMod {p : ℕ} (hp : 0 < p) (l : Terms) :
    toPoly p (l.map fun t ↦ (negMod p t.1, t.2)) = -toPoly p l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPoly_cons, natCast_negMod hp, ih, C_neg]; ring

/-- The terms `(-cᵢ, eᵢ + 1)` denote `-(X · P)`. -/
private theorem toPoly_map_negMod_succ {p : ℕ} (hp : 0 < p) (l : Terms) :
    toPoly p (l.map fun t ↦ (negMod p t.1, t.2 + 1)) = -(X * toPoly p l) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPoly_cons, natCast_negMod hp, ih, C_neg, pow_succ]; ring

/-- The displayed `f`-terms denote `P(X^p) - P(X)`. -/
theorem toPoly_fTermsRaw {p : ℕ} (hp : 0 < p) (l : Terms) :
    toPoly p (fTermsRaw p l) = (toPoly p l).comp (X ^ p) - toPoly p l := by
  rw [fTermsRaw, toPoly_append, toPoly_map_mul_exp, toPoly_map_negMod hp, sub_eq_add_neg]

/-- The displayed `g`-terms denote `(X^p - X)·P(X)`. -/
theorem toPoly_gTermsRaw {p : ℕ} (hp : 0 < p) (l : Terms) :
    toPoly p (gTermsRaw p l) = (X ^ p - X) * toPoly p l := by
  rw [gTermsRaw, toPoly_append, toPoly_map_add_exp, toPoly_map_negMod_succ hp, sub_mul,
    sub_eq_add_neg]

theorem bridgeTerms_of_normalize_eq_nil {p : ℕ} {l : Terms} (h : normalize p l = []) :
    bridgeTerms p l = guardedTerms := by
  simp [bridgeTerms, h]

theorem bridgeTerms_of_normalize_ne_nil {p : ℕ} {l : Terms} (h : normalize p l ≠ []) :
    bridgeTerms p l =
      (normalize p (fTermsRaw p (normalize p l)), normalize p (gTermsRaw p (normalize p l))) := by
  simp [bridgeTerms, h]

/-- **The algorithm computes `f_P`** (semantics of the first output). -/
theorem toPoly_bridgeTerms_fst {p : ℕ} [Fact p.Prime] (l : Terms) :
    toPoly p (bridgeTerms p l).1 = fP (toPoly p l) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h : normalize p l = []
  · rw [bridgeTerms_of_normalize_eq_nil h, (toPoly_eq_zero_iff_normalize_eq_nil hp l).2 h, fP_zero]
    simp [guardedTerms]
  · have hP : toPoly p l ≠ 0 := fun h0 ↦ h ((toPoly_eq_zero_iff_normalize_eq_nil hp l).1 h0)
    rw [bridgeTerms_of_normalize_ne_nil h, fP_of_ne_zero hP]
    simp only [toPoly_normalize, toPoly_fTermsRaw hp]

/-- **The algorithm computes `g_P`** (semantics of the second output). -/
theorem toPoly_bridgeTerms_snd {p : ℕ} [Fact p.Prime] (l : Terms) :
    toPoly p (bridgeTerms p l).2 = gP (toPoly p l) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h : normalize p l = []
  · rw [bridgeTerms_of_normalize_eq_nil h, (toPoly_eq_zero_iff_normalize_eq_nil hp l).2 h, gP_zero]
    simp [guardedTerms]
  · have hP : toPoly p l ≠ 0 := fun h0 ↦ h ((toPoly_eq_zero_iff_normalize_eq_nil hp l).1 h0)
    rw [bridgeTerms_of_normalize_ne_nil h, gP_of_ne_zero hP]
    simp only [toPoly_normalize, toPoly_gTermsRaw hp]

/-- Both outputs are canonical term lists whose coefficients are reduced modulo `p`. -/
theorem normalized_bridgeTerms_fst {p : ℕ} (hp : 1 < p) (l : Terms) :
    Normalized p (bridgeTerms p l).1 := by
  by_cases h : normalize p l = []
  · rw [bridgeTerms_of_normalize_eq_nil h]
    exact ⟨List.pairwise_singleton _ _, by simp [guardedTerms, hp]⟩
  · rw [bridgeTerms_of_normalize_ne_nil h]
    exact normalized_normalize (by omega) _

theorem normalized_bridgeTerms_snd {p : ℕ} (hp : 1 < p) (l : Terms) :
    Normalized p (bridgeTerms p l).2 := by
  by_cases h : normalize p l = []
  · rw [bridgeTerms_of_normalize_eq_nil h]
    exact ⟨List.pairwise_singleton _ _, by simp [guardedTerms, hp]⟩
  · rw [bridgeTerms_of_normalize_ne_nil h]
    exact normalized_normalize (by omega) _

/-- **At most `2t` terms** (list form, `P ≠ 0`): the collected `f`-list has at most twice as many
entries as the normalized input. -/
theorem length_bridgeTerms_fst_le {p : ℕ} {l : Terms} (h : normalize p l ≠ []) :
    (bridgeTerms p l).1.length ≤ 2 * (normalize p l).length := by
  rw [bridgeTerms_of_normalize_ne_nil h]
  exact (length_normalize_le _ _).trans (length_fTermsRaw _ _).le

theorem length_bridgeTerms_snd_le {p : ℕ} {l : Terms} (h : normalize p l ≠ []) :
    (bridgeTerms p l).2.length ≤ 2 * (normalize p l).length := by
  rw [bridgeTerms_of_normalize_ne_nil h]
  exact (length_normalize_le _ _).trans (length_gTermsRaw _ _).le

/-- The support of `expand R p P` lies in the support of `P` scaled by `p`. -/
private theorem support_expand_subset {R : Type*} [CommSemiring R] {p : ℕ} (hp : 0 < p)
    (P : R[X]) : (expand R p P).support ⊆ P.support.image (· * p) := by
  intro n hn
  rw [mem_support_iff, coeff_expand hp] at hn
  split_ifs at hn with hd
  · exact Finset.mem_image.2 ⟨n / p, mem_support_iff.2 hn, Nat.div_mul_cancel hd⟩
  · exact absurd rfl hn

/-- The support of `X ^ k * P` lies in the support of `P` shifted by `k`. -/
private theorem support_X_pow_mul_subset {R : Type*} [Semiring R] (k : ℕ) (P : R[X]) :
    (X ^ k * P).support ⊆ P.support.image (· + k) := by
  intro n hn
  rw [mem_support_iff, coeff_X_pow_mul'] at hn
  split_ifs at hn with hk
  · exact Finset.mem_image.2 ⟨n - k, mem_support_iff.2 hn, Nat.sub_add_cancel hk⟩
  · exact absurd rfl hn

/-- **At most `2t` terms** (polynomial form): `f_P` has at most twice the support of `P ≠ 0`. -/
theorem card_support_fP_le {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} (hP : P ≠ 0) :
    (fP P).support.card ≤ 2 * P.support.card := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [fP_of_ne_zero hP, ← expand_eq_comp_X_pow, sub_eq_add_neg, two_mul]
  refine (Finset.card_le_card support_add).trans ((Finset.card_union_le _ _).trans ?_)
  refine add_le_add ((Finset.card_le_card (support_expand_subset hp P)).trans
    Finset.card_image_le) ?_
  rw [support_neg]

/-- **At most `2t` terms** (polynomial form): `g_P` has at most twice the support of `P ≠ 0`. -/
theorem card_support_gP_le {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} (hP : P ≠ 0) :
    (gP P).support.card ≤ 2 * P.support.card := by
  rw [gP_of_ne_zero hP, sub_mul, sub_eq_add_neg, two_mul]
  refine (Finset.card_le_card support_add).trans ((Finset.card_union_le _ _).trans ?_)
  refine add_le_add ((Finset.card_le_card (support_X_pow_mul_subset p P)).trans
    Finset.card_image_le) ?_
  rw [support_neg, ← pow_one (X : (ZMod p)[X])]
  exact (Finset.card_le_card (support_X_pow_mul_subset 1 P)).trans Finset.card_image_le

/-- Guarded case: `f_0 = 1` has one term. -/
theorem card_support_fP_zero {p : ℕ} [Fact p.Prime] :
    (fP (0 : (ZMod p)[X])).support.card = 1 := by
  rw [fP_zero, ← C_1, support_C one_ne_zero, Finset.card_singleton]

/-- Guarded case: `g_0 = X` has one term. -/
theorem card_support_gP_zero {p : ℕ} [Fact p.Prime] :
    (gP (0 : (ZMod p)[X])).support.card = 1 := by
  rw [gP_zero, support_X, Finset.card_singleton]

/-- The paper's target degree bound `D′ = 1 + max {pD, p + D, 1}`. -/
def targetDegreeBound (p D : ℕ) : ℕ := 1 + max (p * D) (max (p + D) 1)

/-- `deg f_P < D′` whenever `deg P < D` (including the guarded case). -/
theorem natDegree_fP_lt_targetDegreeBound {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} {D : ℕ}
    (hD : P.natDegree < D) : (fP P).natDegree < targetDegreeBound p D := by
  unfold targetDegreeBound
  by_cases hP : P = 0
  · subst hP; rw [fP_zero, natDegree_one]; omega
  · have h1 := natDegree_fP_le hP
    have h2 : p * P.natDegree ≤ p * D := Nat.mul_le_mul_left p hD.le
    omega

/-- `deg g_P < D′` whenever `deg P < D` (including the guarded case). -/
theorem natDegree_gP_lt_targetDegreeBound {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} {D : ℕ}
    (hD : P.natDegree < D) : (gP P).natDegree < targetDegreeBound p D := by
  unfold targetDegreeBound
  by_cases hP : P = 0
  · subst hP; rw [gP_zero, natDegree_X]; omega
  · have h1 := natDegree_gP_le hP
    omega

/-- **Bit length of `D′`**: `log D′ = O(log p + log (D + 1))`, in the concrete form
`size D′ ≤ size p + size (D + 1) + 2`. -/
theorem size_targetDegreeBound_le (p D : ℕ) :
    Nat.size (targetDegreeBound p D) ≤ Nat.size p + Nat.size (D + 1) + 2 := by
  rw [Nat.size_le, pow_add, pow_add, targetDegreeBound]
  have hA := Nat.lt_size_self p
  have hB := Nat.lt_size_self (D + 1)
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h4]
  set A := 2 ^ Nat.size p
  set B := 2 ^ Nat.size (D + 1)
  have hAB : (p + 1) * (D + 2) ≤ A * B := Nat.mul_le_mul hA hB
  have hexp : (p + 1) * (D + 2) = p * D + 2 * p + D + 2 := by ring
  omega

end SparseDiv
