import SparseGcd.Poly.Encoding

/-!
# Boolean roots ↔ assignments (Lemma 16 / Lemma 23, bijection)

The roots of `R = X^E - 1` in `𝔽_p` are exactly `ω^a`, `a < E`. The root `ω^a` is a common root
of all `B_i` iff `a mod ℓ_i ∈ {0, 1}` for every `i`; by the Chinese remainder theorem these roots
are in bijection with `BitString m` (`α_i = true ↔ a ≡ 1 (mod ℓ_i)`), and on such a root the clause
polynomial `P_C` vanishes iff the clause is satisfied.
-/

open Complexity SAT Polynomial Finset

namespace SparseGcd

namespace RootData

variable (d : RootData)

/-! ### Arithmetic of the primes -/

theorem prime_eq_getElem {i : ℕ} (hi : i < d.m) : d.prime i = d.ℓ[i]'hi :=
  List.getD_eq_getElem _ _ hi

/-- `[ℓ_0, …, ℓ_{m-1}]` recovered from `prime`. -/
theorem map_prime_range : (List.range d.m).map d.prime = d.ℓ := by
  apply List.ext_getElem
  · simp [m]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact d.prime_eq_getElem h₂

theorem prime_pos (i : ℕ) : 0 < d.prime i := lt_of_lt_of_le two_pos (d.two_le_prime i)

theorem pairwise_coprime_prime :
    (List.range d.m).Pairwise (Function.onFun Nat.Coprime d.prime) := by
  have := pairwise_coprime_of_nodup d.hprime d.hnodup
  rw [← d.map_prime_range, List.pairwise_map] at this
  exact this

/-! ### CRT -/

/-- Existence part of CRT for the distinct primes. -/
theorem exists_residue (f : Fin d.m → ℕ) (hf : ∀ i, f i < d.prime i) :
    ∃ a, a < d.E ∧ ∀ i : Fin d.m, a % d.prime i = f i := by
  classical
  let g : ℕ → ℕ := fun i ↦ if h : i < d.m then f ⟨i, h⟩ else 0
  refine ⟨Nat.chineseRemainderOfList g d.prime (List.range d.m) d.pairwise_coprime_prime,
    ?_, fun i ↦ ?_⟩
  · have := Nat.chineseRemainderOfList_lt_prod g d.prime (List.range d.m)
      d.pairwise_coprime_prime (fun i _ ↦ (d.prime_pos i).ne')
    rwa [d.map_prime_range] at this
  · have h := (Nat.chineseRemainderOfList g d.prime (List.range d.m) d.pairwise_coprime_prime).2
      i (List.mem_range.2 i.isLt)
    rw [Nat.ModEq] at h
    rw [h]
    simp only [g, dite_eq_left i.isLt]
    exact Nat.mod_eq_of_lt (hf i)

/-- Uniqueness part of CRT. -/
theorem residue_unique {a b : ℕ} (ha : a < d.E) (hb : b < d.E)
    (h : ∀ i : Fin d.m, a % d.prime i = b % d.prime i) : a = b := by
  refine Nat.ModEq.eq_of_lt_of_lt ?_ ha hb
  rw [E, Nat.modEq_list_prod_iff (pairwise_coprime_of_nodup d.hprime d.hnodup)]
  intro i
  have := h i
  rwa [d.prime_eq_getElem i.isLt] at this

/-- The CRT residue `a < E` with `a ≡ (if α_i then 1 else 0) (mod ℓ_i)` for every `i < m`. -/
noncomputable def crtResidue (α : BitString d.m) : ℕ := by
  classical
  exact if h : ∃ a, a < d.E ∧ ∀ i : Fin d.m, a % d.prime i = (if α i then 1 else 0) then
    Classical.choose h else 0

theorem crtResidue_spec (α : BitString d.m) :
    ∃ a, a < d.E ∧ ∀ i : Fin d.m, a % d.prime i = (if α i then 1 else 0) :=
  d.exists_residue (fun i ↦ if α i then 1 else 0) fun i ↦ by
    have := d.two_le_prime i
    split_ifs <;> omega

theorem crtResidue_lt (α : BitString d.m) : d.crtResidue α < d.E := by
  unfold crtResidue
  rw [dite_eq_left (d.crtResidue_spec α)]
  exact (Classical.choose_spec (d.crtResidue_spec α)).1

theorem crtResidue_mod (α : BitString d.m) (i : Fin d.m) :
    d.crtResidue α % d.prime i = if α i then 1 else 0 := by
  unfold crtResidue
  rw [dite_eq_left (d.crtResidue_spec α)]
  exact (Classical.choose_spec (d.crtResidue_spec α)).2 i

/-- The root attached to an assignment. -/
noncomputable def assignRoot (α : BitString d.m) : ZMod d.p := d.ω ^ d.crtResidue α

theorem assignRoot_injective : Function.Injective d.assignRoot := by
  intro α β h
  have hab : d.crtResidue α = d.crtResidue β := by
    have := (pow_eq_pow_iff_mod d.orderOf_ω d.E_pos _ _).1 h
    rwa [Nat.mod_eq_of_lt (d.crtResidue_lt α), Nat.mod_eq_of_lt (d.crtResidue_lt β)] at this
  funext i
  have hi := d.crtResidue_mod α i
  rw [hab, d.crtResidue_mod β i] at hi
  revert hi
  cases α i <;> cases β i <;> simp

theorem assignRoot_ne_zero (α : BitString d.m) : d.assignRoot α ≠ 0 :=
  pow_ne_zero _ d.ω_ne_zero

/-! ### Roots of `R` -/

theorem eval_R (x : ZMod d.p) : d.R.eval x = x ^ d.E - 1 := by
  simp [R]

/-- Roots of `R` are the powers of `ω`. -/
theorem eval_R_eq_zero_iff (x : ZMod d.p) : d.R.eval x = 0 ↔ ∃ a, a < d.E ∧ x = d.ω ^ a := by
  rw [eval_R, sub_eq_zero]
  constructor
  · intro h
    have : NeZero d.E := ⟨d.E_pos.ne'⟩
    obtain ⟨a, ha, rfl⟩ := d.isPrimitiveRoot_ω.eq_pow_of_pow_eq_one h
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, d.isPrimitiveRoot_ω.pow_eq_one, one_pow]

theorem eval_R_assignRoot (α : BitString d.m) : d.R.eval (d.assignRoot α) = 0 :=
  (d.eval_R_eq_zero_iff _).2 ⟨_, d.crtResidue_lt α, rfl⟩

/-- The root set of `R` as a finset. -/
theorem nthRootsFinset_E : nthRootsFinset d.E (1 : ZMod d.p) = (range d.E).image (d.ω ^ ·) := by
  ext x
  rw [mem_nthRootsFinset d.E_pos, mem_image, ← sub_eq_zero, ← eval_R, eval_R_eq_zero_iff]
  simp only [mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

theorem card_nthRootsFinset_E : (nthRootsFinset d.E (1 : ZMod d.p)).card = d.E :=
  d.isPrimitiveRoot_ω.card_nthRootsFinset

theorem mem_nthRootsFinset_iff (x : ZMod d.p) :
    x ∈ nthRootsFinset d.E (1 : ZMod d.p) ↔ d.R.eval x = 0 := by
  rw [mem_nthRootsFinset d.E_pos, eval_R, sub_eq_zero]

/-! ### The Boolean polynomials `B_i` -/

theorem pow_pow_E_div_prime (i a : ℕ) : (d.ω ^ a) ^ (d.E / d.prime i) = d.z i ^ a := by
  rw [z, pow_right_comm]

theorem z_pow_eq_one_iff {i : ℕ} (hi : i < d.m) (a : ℕ) :
    d.z i ^ a = 1 ↔ a % d.prime i = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, d.orderOf_z hi, Nat.dvd_iff_mod_eq_zero]

theorem z_pow_eq_self_iff {i : ℕ} (hi : i < d.m) (a : ℕ) :
    d.z i ^ a = d.z i ↔ a % d.prime i = 1 := by
  have h2 := d.two_le_prime i
  have := pow_eq_pow_iff_mod (d.orderOf_z hi) (d.prime_pos i) a 1
  rwa [pow_one, Nat.mod_eq_of_lt (by omega : 1 < d.prime i)] at this

/-- `B_i(ω^a) = 0 ↔ a mod ℓ_i ∈ {0,1}` (for `i < m`). -/
theorem eval_B_pow_eq_zero_iff {i : ℕ} (hi : i < d.m) (a : ℕ) :
    (d.B i).eval (d.ω ^ a) = 0 ↔ a % d.prime i = 0 ∨ a % d.prime i = 1 := by
  simp only [B, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C, pow_pow_E_div_prime,
    mul_eq_zero, sub_eq_zero]
  rw [d.z_pow_eq_one_iff hi, d.z_pow_eq_self_iff hi]

/-- The common roots of `R` and all `B_i` are exactly the `assignRoot α`. -/
theorem eval_B_eq_zero_forall_iff (x : ZMod d.p) (hx : d.R.eval x = 0) :
    (∀ i, i < d.m → (d.B i).eval x = 0) ↔ ∃ α : BitString d.m, x = d.assignRoot α := by
  obtain ⟨a, ha, rfl⟩ := (d.eval_R_eq_zero_iff x).1 hx
  constructor
  · intro hB
    let α : BitString d.m := fun i ↦ decide (a % d.prime i = 1)
    refine ⟨α, ?_⟩
    unfold assignRoot
    congr 1
    refine d.residue_unique ha (d.crtResidue_lt α) fun i ↦ ?_
    rw [d.crtResidue_mod α i]
    have := (d.eval_B_pow_eq_zero_iff i.isLt a).1 (hB i i.isLt)
    simp only [α, decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact this.resolve_right h
  · rintro ⟨α, hα⟩ i hi
    rw [hα, assignRoot, d.eval_B_pow_eq_zero_iff hi, d.crtResidue_mod α ⟨i, hi⟩]
    split_ifs <;> simp

theorem eval_B_assignRoot (α : BitString d.m) {i : ℕ} (hi : i < d.m) :
    (d.B i).eval (d.assignRoot α) = 0 :=
  (d.eval_B_eq_zero_forall_iff _ (d.eval_R_assignRoot α)).2 ⟨α, rfl⟩ i hi

/-! ### Literal and clause polynomials -/

/-- A literal factor vanishes on `assignRoot α` iff the literal is true under `α`. -/
theorem eval_litPoly_assignRoot (α : BitString d.m) {l : Lit} (hl : l.var < d.m) :
    (d.litPoly l).eval (d.assignRoot α) = 0 ↔ Lit.eval (assignOf α) l = true := by
  have hmod := d.crtResidue_mod α ⟨l.var, hl⟩
  simp only [litPoly, assignRoot, eval_sub, eval_pow, eval_X, eval_C, pow_pow_E_div_prime,
    sub_eq_zero, Lit.eval, get_assignOf, toFun, dite_eq_left hl]
  obtain ⟨s, v⟩ := l
  simp only at hmod hl ⊢
  cases s
  · rw [ite_eq_right Bool.false_ne_true, d.z_pow_eq_one_iff hl, hmod]
    cases α ⟨v, hl⟩ <;> simp
  · rw [ite_eq_left rfl, d.z_pow_eq_self_iff hl, hmod]
    cases α ⟨v, hl⟩ <;> simp

/-- A clause polynomial vanishes on `assignRoot α` iff the clause is satisfied. -/
theorem eval_clausePoly_assignRoot (α : BitString d.m) {c : Clause} (hc : ∀ l ∈ c, l.var < d.m) :
    (d.clausePoly c).eval (d.assignRoot α) = 0 ↔ Clause.eval (assignOf α) c = true := by
  simp only [clausePoly, eval_list_prod, List.map_map, List.prod_eq_zero_iff, List.mem_map,
    Function.comp, Clause.eval, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, (d.eval_litPoly_assignRoot α (hc l hl)).1 h⟩
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, (d.eval_litPoly_assignRoot α (hc l hl)).2 h⟩

/-! ### Common zeros -/

/-- Common zeros of a list of polynomials among the roots of `R`. -/
noncomputable def commonZeros (Fs : List (ZMod d.p)[X]) : Finset (ZMod d.p) :=
  (nthRootsFinset d.E (1 : ZMod d.p)).filter fun x ↦ ∀ F ∈ Fs, F.eval x = 0

theorem mem_solutions_iff_eval {ψ : CNF} {n : ℕ} {α : BitString n} :
    α ∈ solutions ψ n ↔ ∀ c ∈ ψ, Clause.eval (assignOf α) c = true := by
  simp [solutions, CNF.eval]

/-- **Bijection (Lemma 16/23).** The common zeros of `R` and the constraint list are the images
of the satisfying assignments. -/
theorem commonZeros_constraintPolys {ψ : CNF} (hψ : CNF.VarsLt ψ d.m) :
    d.commonZeros (d.constraintPolys ψ) = (solutions ψ d.m).image d.assignRoot := by
  ext x
  rw [commonZeros, mem_filter, mem_nthRootsFinset_iff, mem_image]
  simp only [constraintPolys, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨hx, hF⟩
    have hB : ∀ i, i < d.m → (d.B i).eval x = 0 := fun i hi ↦ hF _ (Or.inl ⟨i, hi, rfl⟩)
    obtain ⟨α, rfl⟩ := (d.eval_B_eq_zero_forall_iff x hx).1 hB
    refine ⟨α, mem_solutions_iff_eval.2 fun c hc ↦ ?_, rfl⟩
    exact (d.eval_clausePoly_assignRoot α (hψ c hc)).1 (hF _ (Or.inr ⟨c, hc, rfl⟩))
  · rintro ⟨α, hα, rfl⟩
    refine ⟨d.eval_R_assignRoot α, ?_⟩
    rintro F (⟨i, hi, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact d.eval_B_assignRoot α hi
    · exact (d.eval_clausePoly_assignRoot α (hψ c hc)).2 (mem_solutions_iff_eval.1 hα c hc)

theorem card_commonZeros_constraintPolys {ψ : CNF} (hψ : CNF.VarsLt ψ d.m) :
    (d.commonZeros (d.constraintPolys ψ)).card = (solutions ψ d.m).card := by
  rw [d.commonZeros_constraintPolys hψ, card_image_of_injective _ d.assignRoot_injective]

theorem commonZeros_eq_empty_iff {ψ : CNF} (hψ : CNF.VarsLt ψ d.m) :
    d.commonZeros (d.constraintPolys ψ) = ∅ ↔ solutions ψ d.m = ∅ := by
  rw [d.commonZeros_constraintPolys hψ, image_eq_empty]

theorem commonZeros_eq_singleton_of_uniqueSat {ψ : CNF} (hψ : CNF.VarsLt ψ d.m)
    (hu : UniqueSat ψ d.m) :
    ∃ α : ZMod d.p, α ≠ 0 ∧ d.commonZeros (d.constraintPolys ψ) = {α} := by
  obtain ⟨α, hα⟩ := card_eq_one.1 hu
  exact ⟨d.assignRoot α, d.assignRoot_ne_zero α, by
    rw [d.commonZeros_constraintPolys hψ, hα, image_singleton]⟩

end RootData

end SparseGcd
