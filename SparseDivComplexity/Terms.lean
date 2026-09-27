import Mathlib
import SparseDivComplexity.Bridge

/-!
# Sparse term lists and their polynomial semantics

This module is the *sparse representation* layer of the paper's Lemma 4 (`lem:bridge`). A sparse
polynomial over `𝔽_p` is given as a list of coefficient–exponent pairs `(c, e)` with natural-number
coefficients (interpreted modulo `p`) and natural-number exponents. Lists may contain repeated
exponents and zero coefficients; `normalize` merges like terms and deletes zero coefficients.

## Main definitions

* `SparseDiv.Terms` — term lists `List (ℕ × ℕ)`.
* `SparseDiv.toPoly p l` — the polynomial `∑ (c, e) ∈ l, C (c : ZMod p) * X ^ e`.
* `SparseDiv.insertTerm`, `SparseDiv.normalize` — collection of like terms, keeping the list strictly
  sorted by exponent with coefficients in `[1, p)`.
* `SparseDiv.Normalized p l` — the canonical-form predicate.

## Main results

* `toPoly_normalize` — normalization preserves the polynomial semantics.
* `normalized_normalize` — normalization produces canonical lists (for `0 < p`).
* `card_support_toPoly_eq_length_normalize` — the number of nonzero terms of the polynomial is the
  length of the normalized list.
* `toPoly_eq_zero_iff_normalize_eq_nil` — the zero test.
-/

open Polynomial

namespace SparseDiv

/-- A sparse term list: coefficient–exponent pairs, coefficients read modulo the prime. -/
abbrev Terms := List (ℕ × ℕ)

/-- The polynomial over `ZMod p` denoted by a term list: `∑ (c, e) ∈ l, C (c : ZMod p) * X ^ e`. -/
noncomputable def toPoly (p : ℕ) (l : Terms) : (ZMod p)[X] :=
  (l.map fun t ↦ C ((t.1 : ℕ) : ZMod p) * X ^ t.2).sum

@[simp] theorem toPoly_nil (p : ℕ) : toPoly p [] = 0 := by
  simp [toPoly]

@[simp] theorem toPoly_cons (p : ℕ) (t : ℕ × ℕ) (l : Terms) :
    toPoly p (t :: l) = C ((t.1 : ℕ) : ZMod p) * X ^ t.2 + toPoly p l := by
  simp [toPoly]

theorem toPoly_append (p : ℕ) (l₁ l₂ : Terms) :
    toPoly p (l₁ ++ l₂) = toPoly p l₁ + toPoly p l₂ := by
  simp [toPoly]

/-- The coefficient of `X ^ n` in `toPoly p l` is the sum (in `ZMod p`) of the coefficients of the
terms of `l` with exponent `n`. -/
theorem coeff_toPoly (p : ℕ) (l : Terms) (n : ℕ) :
    (toPoly p l).coeff n = ((l.filter fun t ↦ t.2 = n).map fun t ↦ ((t.1 : ℕ) : ZMod p)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [toPoly_cons, coeff_add, ih, coeff_C_mul, coeff_X_pow]
    by_cases h : t.2 = n
    · simp [h]
    · simp [h, Ne.symm h]

/-- Insert the term `c · X ^ e` into a term list kept strictly sorted by exponent: the coefficient is
reduced modulo `p`, like terms are merged, and zero coefficients are dropped. -/
def insertTerm (p : ℕ) (c e : ℕ) : Terms → Terms
  | [] => if c % p = 0 then [] else [(c % p, e)]
  | (c', e') :: rest =>
    if e < e' then (if c % p = 0 then (c', e') :: rest else (c % p, e) :: (c', e') :: rest)
    else if e = e' then (if (c + c') % p = 0 then rest else ((c + c') % p, e) :: rest)
    else (c', e') :: insertTerm p c e rest

/-- Collect like terms: the canonical sorted representation of the polynomial `toPoly p l`. -/
def normalize (p : ℕ) : Terms → Terms
  | [] => []
  | (c, e) :: rest => insertTerm p c e (normalize p rest)

/-- Canonical term lists: strictly increasing exponents and coefficients in `[1, p)`. -/
def Normalized (p : ℕ) (l : Terms) : Prop :=
  l.Pairwise (fun s t ↦ s.2 < t.2) ∧ ∀ t ∈ l, 0 < t.1 ∧ t.1 < p

instance (p : ℕ) (l : Terms) : Decidable (Normalized p l) := by
  unfold Normalized; infer_instance

/-- Inserting a term adds the corresponding monomial. -/
theorem toPoly_insertTerm (p c e : ℕ) (l : Terms) :
    toPoly p (insertTerm p c e l) = C ((c : ℕ) : ZMod p) * X ^ e + toPoly p l := by
  have hmod : ∀ a : ℕ, ((a % p : ℕ) : ZMod p) = (a : ZMod p) := fun a ↦ ZMod.natCast_mod a p
  induction l with
  | nil =>
    simp only [insertTerm]
    split_ifs with h
    · rw [toPoly_nil, ← hmod c, h]; simp
    · simp [hmod]
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTerm]
    split_ifs with h₁ h₂ h₃ h₄
    · rw [← hmod c, h₂]; simp
    · rw [toPoly_cons, hmod]
    · rw [toPoly_cons]
      dsimp only
      rw [← h₃, ← add_assoc, ← add_mul, ← C_add, ← Nat.cast_add, ← hmod, h₄]
      simp
    · rw [toPoly_cons, toPoly_cons, hmod, Nat.cast_add, C_add, add_mul, add_assoc, h₃]
    · rw [toPoly_cons, ih, toPoly_cons, add_left_comm]

/-- **Normalization preserves the polynomial.** -/
theorem toPoly_normalize (p : ℕ) (l : Terms) : toPoly p (normalize p l) = toPoly p l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    simp only [normalize]
    rw [toPoly_insertTerm, ih, toPoly_cons]

/-- Every exponent occurring in `insertTerm p c e l` is either `e` or an exponent of `l`. -/
private theorem snd_of_mem_insertTerm {p c e : ℕ} {l : Terms} {t : ℕ × ℕ}
    (ht : t ∈ insertTerm p c e l) : t.2 = e ∨ ∃ s ∈ l, t.2 = s.2 := by
  induction l with
  | nil =>
    simp only [insertTerm] at ht
    split_ifs at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht
      exact Or.inl (by rw [ht])
  | cons s l ih =>
    obtain ⟨c', e'⟩ := s
    simp only [insertTerm] at ht
    split_ifs at ht
    · exact Or.inr ⟨t, ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inr ⟨_, List.mem_cons_self .., rfl⟩
      · rcases ih ht with h | ⟨u, hu, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, h⟩

/-- Insertion preserves canonicity (for a positive modulus). -/
theorem normalized_insertTerm {p : ℕ} (hp : 0 < p) (c e : ℕ) {l : Terms}
    (h : Normalized p l) : Normalized p (insertTerm p c e l) := by
  induction l with
  | nil =>
    simp only [insertTerm]
    split_ifs with h0
    · exact ⟨List.Pairwise.nil, by simp⟩
    · exact ⟨List.pairwise_singleton _ _, by simp [Nat.pos_of_ne_zero h0, Nat.mod_lt _ hp]⟩
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    obtain ⟨hpw, hb⟩ := h
    rw [List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw⟩ := hpw
    have hl : Normalized p l := ⟨hpw, fun t ht ↦ hb t (List.mem_cons_of_mem _ ht)⟩
    have hb' := hb (c', e') (List.mem_cons_self ..)
    simp only [insertTerm]
    split_ifs with h₁ h₂ h₃ h₄
    · exact ⟨List.pairwise_cons.mpr ⟨hlt, hpw⟩, hb⟩
    · refine ⟨List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨hlt, hpw⟩⟩, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h₁
        · exact h₁.trans (hlt s hs)
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨Nat.pos_of_ne_zero h₂, Nat.mod_lt _ hp⟩
        · exact hb s hs
    · exact hl
    · refine ⟨List.pairwise_cons.mpr ⟨fun s hs ↦ h₃ ▸ hlt s hs, hpw⟩, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨Nat.pos_of_ne_zero h₄, Nat.mod_lt _ hp⟩
      · exact hb s (List.mem_cons_of_mem _ hs)
    · obtain ⟨hpw', hb''⟩ := ih hl
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw'⟩, ?_⟩
      · intro s hs
        rcases snd_of_mem_insertTerm hs with hs | ⟨u, hu, hs⟩
        · show e' < s.2
          rw [hs]; omega
        · show e' < s.2
          rw [hs]; exact hlt u hu
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hb'
        · exact hb'' s hs

/-- **Normalization produces canonical lists** (for a positive modulus). -/
theorem normalized_normalize {p : ℕ} (hp : 0 < p) (l : Terms) : Normalized p (normalize p l) := by
  induction l with
  | nil => exact ⟨List.Pairwise.nil, by simp [normalize]⟩
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    exact normalized_insertTerm hp c e ih

theorem length_insertTerm_le (p c e : ℕ) (l : Terms) :
    (insertTerm p c e l).length ≤ l.length + 1 := by
  induction l with
  | nil =>
    simp only [insertTerm]
    split_ifs <;> simp
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTerm]
    split_ifs <;> simp only [List.length_cons] <;> omega

/-- Collection never increases the number of terms. -/
theorem length_normalize_le (p : ℕ) (l : Terms) : (normalize p l).length ≤ l.length := by
  induction l with
  | nil => simp [normalize]
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    simp only [normalize, List.length_cons]
    exact (length_insertTerm_le p c e _).trans (Nat.succ_le_succ ih)

/-- In a list with strictly increasing exponents, at most one term has a given exponent. -/
private theorem filter_snd_eq_of_pairwise {l : Terms} (hl : l.Pairwise fun s t ↦ s.2 < t.2)
    (n : ℕ) :
    l.filter (fun t ↦ t.2 = n) = [] ∨ ∃ t ∈ l, t.2 = n ∧ l.filter (fun t ↦ t.2 = n) = [t] := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ht, hl⟩ := hl
    by_cases h : t.2 = n
    · right
      refine ⟨t, List.mem_cons_self .., h, ?_⟩
      rw [List.filter_cons_of_pos (by simpa using h), List.filter_eq_nil_iff.mpr]
      intro s hs
      have := ht s hs
      simp only [decide_eq_true_eq]
      omega
    · rw [List.filter_cons_of_neg (by simpa using h)]
      rcases ih hl with h' | ⟨s, hs, hsn, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hsn, h'⟩

/-- The support of the polynomial of a canonical list is the set of its exponents. -/
theorem support_toPoly_of_normalized {p : ℕ} {l : Terms} (h : Normalized p l) :
    (toPoly p l).support = (l.map Prod.snd).toFinset := by
  ext n
  rw [mem_support_iff, coeff_toPoly, List.mem_toFinset, List.mem_map]
  rcases filter_snd_eq_of_pairwise h.1 n with h' | ⟨t, ht, htn, h'⟩
  · rw [h']
    simp only [List.map_nil, List.sum_nil, ne_eq, not_true_eq_false, false_iff, not_exists,
      not_and]
    intro t ht htn
    have : t ∈ l.filter (fun t ↦ t.2 = n) := List.mem_filter.mpr ⟨ht, by simpa using htn⟩
    rw [h'] at this
    exact List.not_mem_nil this
  · rw [h']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine ⟨fun _ ↦ ⟨t, ht, htn⟩, fun _ hc ↦ ?_⟩
    obtain ⟨h0, hp⟩ := h.2 t ht
    rw [ZMod.natCast_eq_zero_iff] at hc
    exact absurd (Nat.le_of_dvd h0 hc) (not_le.mpr hp)

/-- A canonical list has exactly as many entries as its polynomial has nonzero terms. -/
theorem card_support_toPoly_of_normalized {p : ℕ} {l : Terms} (h : Normalized p l) :
    (toPoly p l).support.card = l.length := by
  rw [support_toPoly_of_normalized h, List.toFinset_card_of_nodup, List.length_map]
  exact ((List.pairwise_map (R := (· < ·))).mpr h.1).nodup

/-- **Term count after collection.** The number of nonzero terms of `toPoly p l` is the length of the
normalized list. -/
theorem card_support_toPoly_eq_length_normalize {p : ℕ} (hp : 0 < p) (l : Terms) :
    (toPoly p l).support.card = (normalize p l).length := by
  rw [← toPoly_normalize, card_support_toPoly_of_normalized (normalized_normalize hp l)]

/-- The number of nonzero terms never exceeds the number of listed terms. -/
theorem card_support_toPoly_le_length {p : ℕ} (hp : 0 < p) (l : Terms) :
    (toPoly p l).support.card ≤ l.length :=
  (card_support_toPoly_eq_length_normalize hp l).trans_le (length_normalize_le p l)

/-- **Zero test.** A term list denotes the zero polynomial iff its normalization is empty. -/
theorem toPoly_eq_zero_iff_normalize_eq_nil {p : ℕ} (hp : 0 < p) (l : Terms) :
    toPoly p l = 0 ↔ normalize p l = [] := by
  rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero,
    card_support_toPoly_eq_length_normalize hp, List.length_eq_zero_iff]

/-- The coefficient of `X ^ e` in the polynomial of `(c, e) :: l` when every exponent of `l`
exceeds `e`. -/
private theorem coeff_toPoly_cons_self {p c e : ℕ} {l : Terms} (hl : ∀ t ∈ l, e < t.2) :
    (toPoly p ((c, e) :: l)).coeff e = (c : ZMod p) := by
  rw [coeff_toPoly, List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.mpr]
  · simp
  · intro t ht
    have := hl t ht
    simp only [decide_eq_true_eq]
    omega

/-- A canonical list is determined by its polynomial. -/
private theorem eq_of_normalized_of_toPoly_eq {p : ℕ} {l₁ : Terms} :
    ∀ {l₂ : Terms}, Normalized p l₁ → Normalized p l₂ → toPoly p l₁ = toPoly p l₂ → l₁ = l₂ := by
  induction l₁ with
  | nil =>
    intro l₂ _ h₂ h
    have := card_support_toPoly_of_normalized h₂
    rw [← h, toPoly_nil, Polynomial.support_zero, Finset.card_empty] at this
    exact (List.length_eq_zero_iff.mp this.symm).symm
  | cons t₁ l₁ ih =>
    intro l₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      have := card_support_toPoly_of_normalized h₁
      rw [h, toPoly_nil, Polynomial.support_zero, Finset.card_empty] at this
      simp at this
    | cons t₂ l₂ =>
      obtain ⟨c₁, e₁⟩ := t₁
      obtain ⟨c₂, e₂⟩ := t₂
      obtain ⟨hpw₁, hb₁⟩ := h₁
      obtain ⟨hpw₂, hb₂⟩ := h₂
      have hs := support_toPoly_of_normalized ⟨hpw₁, hb₁⟩
      rw [h, support_toPoly_of_normalized ⟨hpw₂, hb₂⟩] at hs
      rw [List.pairwise_cons] at hpw₁ hpw₂
      have he₁ : e₁ = e₂ ∨ e₂ < e₁ := by
        have : e₁ ∈ (((c₂, e₂) :: l₂).map Prod.snd).toFinset := by
          rw [hs]; simp
        simp only [List.mem_toFinset, List.map_cons, List.mem_cons, List.mem_map] at this
        rcases this with h | ⟨t, ht, rfl⟩
        · exact Or.inl h
        · exact Or.inr (hpw₂.1 t ht)
      have he₂ : e₂ = e₁ ∨ e₁ < e₂ := by
        have : e₂ ∈ (((c₁, e₁) :: l₁).map Prod.snd).toFinset := by
          rw [← hs]; simp
        simp only [List.mem_toFinset, List.map_cons, List.mem_cons, List.mem_map] at this
        rcases this with h | ⟨t, ht, rfl⟩
        · exact Or.inl h
        · exact Or.inr (hpw₁.1 t ht)
      have he : e₁ = e₂ := by omega
      subst he
      have hc : c₁ = c₂ := by
        have hcoef := congrArg (fun q ↦ q.coeff e₁) h
        simp only [coeff_toPoly_cons_self hpw₁.1, coeff_toPoly_cons_self hpw₂.1] at hcoef
        have h1 := hb₁ (c₁, e₁) (List.mem_cons_self ..)
        have h2 := hb₂ (c₂, e₁) (List.mem_cons_self ..)
        rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1.2, Nat.mod_eq_of_lt h2.2] at hcoef
      subst hc
      congr 1
      refine ih ⟨hpw₁.2, fun t ht ↦ hb₁ t (List.mem_cons_of_mem _ ht)⟩
        ⟨hpw₂.2, fun t ht ↦ hb₂ t (List.mem_cons_of_mem _ ht)⟩ ?_
      rw [toPoly_cons, toPoly_cons] at h
      exact add_left_cancel h

/-- Canonical lists are fixed by normalization. -/
theorem normalize_of_normalized {p : ℕ} (hp : 0 < p) {l : Terms} (h : Normalized p l) :
    normalize p l = l :=
  eq_of_normalized_of_toPoly_eq (normalized_normalize hp l) h (toPoly_normalize p l)

/-- **Uniqueness of the canonical form**: lists denoting the same polynomial normalize identically. -/
theorem normalize_eq_of_toPoly_eq {p : ℕ} (hp : 0 < p) {l₁ l₂ : Terms}
    (h : toPoly p l₁ = toPoly p l₂) : normalize p l₁ = normalize p l₂ :=
  eq_of_normalized_of_toPoly_eq (normalized_normalize hp l₁) (normalized_normalize hp l₂)
    (by rw [toPoly_normalize, toPoly_normalize, h])

/-- The largest listed exponent bounds the degree. -/
theorem natDegree_toPoly_le (p : ℕ) (l : Terms) :
    (toPoly p l).natDegree ≤ (l.map Prod.snd).foldr max 0 := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [toPoly_cons, List.map_cons, List.foldr_cons]
    exact (natDegree_add_le _ _).trans (max_le_max (natDegree_C_mul_X_pow_le _ _) ih)

/-- Every exponent of a canonical list is at most the degree of its polynomial. -/
theorem exponent_le_natDegree_of_normalized {p : ℕ} {l : Terms} (h : Normalized p l)
    {t : ℕ × ℕ} (ht : t ∈ l) : t.2 ≤ (toPoly p l).natDegree :=
  le_natDegree_of_mem_supp _ (by
    rw [support_toPoly_of_normalized h]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩))

end SparseDiv
