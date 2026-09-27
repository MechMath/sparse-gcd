import SparseGcd.Poly.Roots
import SparseGcd.Poly.Gcd

/-!
# Random compression (Lemma 17 / Lemma 24)

`H = Σ_j u_j F_j`. Every common zero of the `F_j` is a zero of `H`. If `α` is not a common zero
(`F_s(α) ≠ 0` for some `s`), then for every choice of the other coefficients exactly one value of
`u_s` makes `H(α) = 0`; hence for uniform `u_s` the probability is `1/p`, and a union bound over the
`E` roots of `R` gives `Pr[Z(R,H) ≠ Z(R,F)] ≤ E/p`. The probability statements for the actual
(near-uniform) machine sampling are derived from `existsUnique_coeff` in the machine layer.

`R = X^E - 1` splits with distinct roots (Lemma 16), so `gcd(R,H)` is the product of the linear
factors of the common roots; on the success event the gcd is `1` (no satisfying assignment) or
`X - α` (unique satisfying assignment).
-/

open Complexity SAT Polynomial Finset

namespace SparseGcd

namespace RootData

variable (d : RootData)

theorem eval_Hpoly_eq_zero_of_forall (us : List (ZMod d.p)) {Fs : List (ZMod d.p)[X]}
    {α : ZMod d.p} (h : ∀ F ∈ Fs, F.eval α = 0) : (d.Hpoly us Fs).eval α = 0 := by
  unfold Hpoly
  induction us generalizing Fs with
  | nil => simp
  | cons u us ih =>
    cases Fs with
    | nil => simp
    | cons F Fs =>
      simp only [List.zipWith_cons_cons, List.sum_cons, eval_add, eval_mul, eval_C]
      rw [h F (List.mem_cons_self ..), ih (fun F' hF' ↦ h F' (List.mem_cons_of_mem _ hF'))]
      simp

theorem commonZeros_subset_Hpoly (us : List (ZMod d.p)) (Fs : List (ZMod d.p)[X]) :
    d.commonZeros Fs ⊆ d.commonZeros [d.Hpoly us Fs] := by
  intro x hx
  simp only [commonZeros, mem_filter, List.forall_mem_singleton] at hx ⊢
  exact ⟨hx.1, d.eval_Hpoly_eq_zero_of_forall us hx.2⟩

/-- Isolating the `s`-th coefficient of `H`. -/
theorem Hpoly_set (us : List (ZMod d.p)) (Fs : List (ZMod d.p)[X]) {s : ℕ}
    (hs : s < Fs.length) (hs' : s < us.length) (v : ZMod d.p) :
    d.Hpoly (us.set s v) Fs = C v * Fs[s] + d.Hpoly (us.set s 0) Fs := by
  unfold Hpoly
  induction s generalizing us Fs with
  | zero =>
    cases us with
    | nil => simp at hs'
    | cons u us =>
      cases Fs with
      | nil => simp at hs
      | cons F Fs => simp
  | succ s ih =>
    cases us with
    | nil => simp at hs'
    | cons u us =>
      cases Fs with
      | nil => simp at hs
      | cons F Fs =>
        simp only [List.set_cons_succ, List.zipWith_cons_cons, List.sum_cons,
          List.getElem_cons_succ]
        rw [ih us Fs (by simpa using hs) (by simpa using hs')]
        ring

/-- **Exactly one bad value of `u_s`.** -/
theorem existsUnique_coeff (us : List (ZMod d.p)) {Fs : List (ZMod d.p)[X]} {s : ℕ}
    (hs : s < Fs.length) (hlen : us.length = Fs.length) {α : ZMod d.p}
    (hF : (Fs.get ⟨s, hs⟩).eval α ≠ 0) :
    ∃! v : ZMod d.p, (d.Hpoly (us.set s v) Fs).eval α = 0 := by
  rw [List.get_eq_getElem] at hF
  have key : ∀ v, (d.Hpoly (us.set s v) Fs).eval α = 0 ↔
      v = -(d.Hpoly (us.set s 0) Fs).eval α / (Fs[s]).eval α := by
    intro v
    rw [d.Hpoly_set us Fs hs (hlen ▸ hs) v, eval_add, eval_mul, eval_C, eq_div_iff hF,
      add_eq_zero_iff_eq_neg]
  simp_rw [key]
  exact existsUnique_eq

/-- `List.ofFn` of an update is a `List.set`. -/
theorem _root_.List.ofFn_update {β : Type*} {n : ℕ} (u : Fin n → β) (s : Fin n) (v : β) :
    List.ofFn (Function.update u s v) = (List.ofFn u).set s v := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [List.getElem_ofFn, List.getElem_set, List.getElem_ofFn, Function.update_apply]
    have : (⟨i, by simpa using h₁⟩ : Fin n) = s ↔ s.1 = i := by
      rw [Fin.ext_iff]; exact eq_comm
    simp only [this]

/-- For `α` not a common zero of `Fs`, at most a `1/p` fraction of the coefficient vectors `u`
make `H_u(α) = 0` (in fact exactly `p^(t-1)` of them). -/
theorem card_filter_eval_Hpoly_mul_le (Fs : List (ZMod d.p)[X]) {α : ZMod d.p}
    (hα : ∃ F ∈ Fs, F.eval α ≠ 0) :
    ((univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
        (d.Hpoly (List.ofFn u) Fs).eval α = 0).card * d.p ≤ d.p ^ Fs.length := by
  classical
  obtain ⟨F, hF, hFα⟩ := hα
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hF
  set fib := (univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
    (d.Hpoly (List.ofFn u) Fs).eval α = 0 with hfib
  have key : Fintype.card (fib × ZMod d.p) ≤ Fintype.card (Fin Fs.length → ZMod d.p) := by
    refine Fintype.card_le_of_injective (fun x ↦ Function.update x.1.1 ⟨s, hs⟩ x.2) ?_
    rintro ⟨⟨u, hu⟩, v⟩ ⟨⟨u', hu'⟩, v'⟩ h
    simp only at h
    have hv : v = v' := by
      have := congrFun h ⟨s, hs⟩
      simpa using this
    have hoff : ∀ i, i ≠ (⟨s, hs⟩ : Fin Fs.length) → u i = u' i := by
      intro i hi
      have := congrFun h i
      rwa [Function.update_of_ne hi, Function.update_of_ne hi] at this
    have hu'' : Function.update u ⟨s, hs⟩ (u' ⟨s, hs⟩) = u' := by
      funext i
      by_cases hi : i = ⟨s, hs⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi, hoff i hi]
    simp only [hfib, mem_filter, mem_univ, true_and] at hu hu'
    have huniq := d.existsUnique_coeff (List.ofFn u) hs (by simp) (α := α)
      (by rw [List.get_eq_getElem]; exact hFα)
    have hs1 : (d.Hpoly ((List.ofFn u).set s (u ⟨s, hs⟩)) Fs).eval α = 0 := by
      have e : (List.ofFn u).set s (u ⟨s, hs⟩) = List.ofFn u := by
        have := List.ofFn_update u ⟨s, hs⟩ (u ⟨s, hs⟩)
        rw [Function.update_eq_self] at this
        exact this.symm
      rw [e]; exact hu
    have hs2 : (d.Hpoly ((List.ofFn u).set s (u' ⟨s, hs⟩)) Fs).eval α = 0 := by
      have e : (List.ofFn u).set s (u' ⟨s, hs⟩) = List.ofFn u' := by
        have := List.ofFn_update u ⟨s, hs⟩ (u' ⟨s, hs⟩)
        rw [hu''] at this
        exact this.symm
      rw [e]; exact hu'
    have hus : u ⟨s, hs⟩ = u' ⟨s, hs⟩ := huniq.unique hs1 hs2
    have huu : u = u' := by
      funext i
      by_cases hi : i = ⟨s, hs⟩
      · subst hi; exact hus
      · exact hoff i hi
    subst huu; subst hv; rfl
  simpa [Fintype.card_prod, Fintype.card_coe, ZMod.card, Fintype.card_fun, Fintype.card_fin]
    using key

/-- Uniform version (Lemma 17 as stated): over all coefficient vectors `u ∈ 𝔽_p^t`, the fraction
with `Z(R,H) ≠ Z(R,F)` is at most `E/p`. -/
theorem card_bad_coeffs_le (Fs : List (ZMod d.p)[X]) :
    ((univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
        d.commonZeros [d.Hpoly (List.ofFn u) Fs] ≠ d.commonZeros Fs).card * d.p ≤
      d.E * d.p ^ Fs.length := by
  classical
  set S := nthRootsFinset d.E (1 : ZMod d.p) with hS
  have hsub : ((univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
        d.commonZeros [d.Hpoly (List.ofFn u) Fs] ≠ d.commonZeros Fs) ⊆
      (S \ d.commonZeros Fs).biUnion fun α ↦
        (univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
          (d.Hpoly (List.ofFn u) Fs).eval α = 0 := by
    intro u hu
    rw [mem_filter] at hu
    have hss : d.commonZeros Fs ⊂ d.commonZeros [d.Hpoly (List.ofFn u) Fs] :=
      lt_of_le_of_ne (d.commonZeros_subset_Hpoly _ _) (Ne.symm hu.2)
    obtain ⟨α, hα, hαZ⟩ := Finset.exists_of_ssubset hss
    rw [mem_biUnion]
    refine ⟨α, ?_, ?_⟩
    · rw [mem_sdiff]
      refine ⟨?_, hαZ⟩
      simp only [commonZeros, mem_filter] at hα
      exact hα.1
    · simp only [commonZeros, mem_filter, List.forall_mem_singleton] at hα
      simp only [mem_filter, mem_univ, true_and]
      exact hα.2
  calc _ ≤ ((S \ d.commonZeros Fs).biUnion fun α ↦
        (univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
          (d.Hpoly (List.ofFn u) Fs).eval α = 0).card * d.p :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ α ∈ S \ d.commonZeros Fs, ((univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
          (d.Hpoly (List.ofFn u) Fs).eval α = 0).card) * d.p :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ α ∈ S \ d.commonZeros Fs, ((univ : Finset (Fin Fs.length → ZMod d.p)).filter fun u ↦
          (d.Hpoly (List.ofFn u) Fs).eval α = 0).card * d.p := Finset.sum_mul ..
    _ ≤ ∑ α ∈ S \ d.commonZeros Fs, d.p ^ Fs.length := by
        apply Finset.sum_le_sum
        intro α hα
        apply d.card_filter_eval_Hpoly_mul_le
        rw [mem_sdiff] at hα
        have h2 := hα.2
        simp only [commonZeros, mem_filter, not_and, not_forall] at h2
        obtain ⟨F, hF, hFα⟩ := h2 hα.1
        exact ⟨F, hF, hFα⟩
    _ = (S \ d.commonZeros Fs).card * d.p ^ Fs.length := by rw [sum_const, smul_eq_mul]
    _ ≤ d.E * d.p ^ Fs.length := by
        apply Nat.mul_le_mul_right
        rw [← d.card_nthRootsFinset_E]
        exact card_le_card sdiff_subset

/-- `R` as a product of distinct linear factors. -/
theorem R_eq_prod : d.R = ∏ β ∈ nthRootsFinset d.E (1 : ZMod d.p), (X - C β) :=
  X_pow_sub_one_eq_prod_nthRoots d.E_pos d.isPrimitiveRoot_ω

/-- `gcd(R, H)` is the product over the common roots (set, not multiset). -/
theorem monicGcd_R_eq (H : (ZMod d.p)[X]) :
    monicGcd d.R H = ∏ β ∈ d.commonZeros [H], (X - C β) := by
  rw [d.R_eq_prod, monicGcd_prod_filter]
  simp only [commonZeros, List.forall_mem_singleton]

theorem natDegree_monicGcd_R_pos_iff (H : (ZMod d.p)[X]) :
    0 < (monicGcd d.R H).natDegree ↔ (d.commonZeros [H]).Nonempty := by
  rw [d.R_eq_prod, natDegree_monicGcd_prod_pos_iff]
  simp [commonZeros, Finset.Nonempty]

theorem not_isCoprime_R_iff (H : (ZMod d.p)[X]) :
    ¬ IsCoprime d.R H ↔ (d.commonZeros [H]).Nonempty := by
  rw [not_isCoprime_iff_natDegree_monicGcd_pos (Or.inl d.R_ne_zero),
    d.natDegree_monicGcd_R_pos_iff]

theorem monic_R : d.R.Monic := by
  simpa [R] using monic_X_pow_sub_C (1 : ZMod d.p) d.E_pos.ne'

theorem monicGcd_R_zero : monicGcd d.R 0 = d.R := monicGcd_zero_right d.monic_R

/-- **On the success event** `Z(R,H) = Z(R,F)`: no solution ⇒ `gcd = 1`; unique solution ⇒
`gcd = X - α` with `α ≠ 0`. -/
theorem monicGcd_of_success {ψ : CNF} (hψ : CNF.VarsLt ψ d.m) {H : (ZMod d.p)[X]}
    (hZ : d.commonZeros [H] = d.commonZeros (d.constraintPolys ψ)) :
    (solutions ψ d.m = ∅ → monicGcd d.R H = 1) ∧
    (UniqueSat ψ d.m → ∃ α : ZMod d.p, α ≠ 0 ∧ monicGcd d.R H = X - C α) ∧
    (0 < (monicGcd d.R H).natDegree ↔ (solutions ψ d.m).Nonempty) := by
  refine ⟨fun h0 ↦ ?_, fun hu ↦ ?_, ?_⟩
  · rw [d.monicGcd_R_eq, hZ, (d.commonZeros_eq_empty_iff hψ).mpr h0, Finset.prod_empty]
  · obtain ⟨α, hα, hαZ⟩ := d.commonZeros_eq_singleton_of_uniqueSat hψ hu
    exact ⟨α, hα, by rw [d.monicGcd_R_eq, hZ, hαZ, Finset.prod_singleton]⟩
  · rw [d.natDegree_monicGcd_R_pos_iff, hZ, d.commonZeros_constraintPolys hψ,
      Finset.image_nonempty]

/-- The gcd on the success event has at most two terms. -/
theorem length_termsOf_monicGcd_of_success {ψ : CNF} (hψ : CNF.VarsLt ψ d.m) {H : (ZMod d.p)[X]}
    (hZ : d.commonZeros [H] = d.commonZeros (d.constraintPolys ψ))
    (hcard : (solutions ψ d.m).card ≤ 1) :
    (termsOf d.p (monicGcd d.R H)).length ≤ 2 := by
  obtain ⟨h0, h1, -⟩ := d.monicGcd_of_success hψ hZ
  have hp : 1 < d.p := d.hp.one_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hc | hc
  · rw [h0 (Finset.card_eq_zero.mp hc), termsOf_one d.p hp]
    simp
  · obtain ⟨α, hα, hg⟩ := h1 hc
    rw [hg, termsOf_X_sub_C d.p hp hα]
    simp

/-- Off the success event we still know: no solutions ⇒ `Z(R,F) = ∅`, so a common root of `R, H`
must be a non-solution root — used only for bookkeeping. -/
theorem commonZeros_constraint_eq_empty_of_unsat {ψ : CNF} (hψ : CNF.VarsLt ψ d.m)
    (h : ¬ ψ.Satisfiable) : d.commonZeros (d.constraintPolys ψ) = ∅ :=
  (d.commonZeros_eq_empty_iff hψ).mpr ((not_satisfiable_iff_solutions_eq_empty hψ).mp h)

end RootData

end SparseGcd
