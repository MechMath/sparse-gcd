import SparseGcd.Cnf.Basic
import SparseGcd.Field.PrimitiveRoot
import SparseDivComplexity.Terms
import SparseDivComplexity.Languages

/-!
# Sparse polynomial encoding of a bounded-clause CNF (Lemma 16 / Lemma 23, definitions and bounds)

Given root data (`p` prime, Boolean primes `ℓ_0..ℓ_{m-1}`, `E = ∏ ℓ_i`, `ω ∈ 𝔽_p` of exact order
`E`) we define, both as polynomials over `ZMod p` and as sparse term lists (`SparseDiv.Terms`):

* `R = X^E - 1`;
* `z_i = ω^{E/ℓ_i}` and `B_i = (X^{E/ℓ_i} - 1)(X^{E/ℓ_i} - z_i) = X^{2E/ℓ_i} - (1+z_i) X^{E/ℓ_i} + z_i`;
* literal factors `L_{i,1} = X^{E/ℓ_i} - z_i` (positive literal), `L_{i,0} = X^{E/ℓ_i} - 1` (negative);
* clause polynomials `P_C = ∏_{λ ∈ C} L_λ` (empty clause: `P = 1`);
* the constraint list `F = [B_0, …, B_{m-1}, P_{C_1}, …, P_{C_k}]`;
* `H = Σ_j u_j F_j` for coefficients `u_j`.

Support and degree bounds (Lemma 25): `|R| = 2`, `|B_i| ≤ 3`, `|P_C| ≤ 8`, `|H| ≤ 3m + 8k`,
all exponents `≤ 2E`, all coefficients `< p`.
-/

open Complexity SAT Polynomial SparseDiv

namespace SparseGcd

/-- Root data: the field, the Boolean primes and an element `w` of exact order `E = ∏ ℓ_i`. -/
structure RootData where
  p : ℕ
  hp : p.Prime
  /-- Boolean primes `ℓ_0, …, ℓ_{m-1}`. -/
  ℓ : List ℕ
  hprime : ∀ q ∈ ℓ, q.Prime
  hnodup : ℓ.Nodup
  /-- The residue `w` representing `ω`. -/
  w : ℕ
  hw : w < p
  hord : orderOf (w : ZMod p) = ℓ.prod

namespace RootData

variable (d : RootData)

instance : Fact d.p.Prime := ⟨d.hp⟩

/-- Number of Boolean variables. -/
def m : ℕ := d.ℓ.length

/-- `E = ∏ ℓ_i`. -/
def E : ℕ := d.ℓ.prod

/-- `ω ∈ 𝔽_p`. -/
def ω : ZMod d.p := d.w

/-- The `i`-th prime (`2` as a harmless default out of range). -/
def prime (i : ℕ) : ℕ := d.ℓ.getD i 2

/-- `z_i = ω^{E/ℓ_i}`. -/
def z (i : ℕ) : ZMod d.p := d.ω ^ (d.E / d.prime i)

theorem E_pos : 0 < d.E := prod_pos_of_prime d.hprime

theorem prime_prime {i : ℕ} (hi : i < d.m) : (d.prime i).Prime := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi]
  exact d.hprime _ (List.getElem_mem hi)

theorem two_le_prime (i : ℕ) : 2 ≤ d.prime i := by
  unfold prime
  by_cases hi : i < d.ℓ.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact (d.hprime _ (List.getElem_mem hi)).two_le
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]

theorem prime_dvd_E {i : ℕ} (hi : i < d.m) : d.prime i ∣ d.E := by
  unfold prime E
  rw [List.getD_eq_getElem _ _ hi]
  exact List.dvd_prod (List.getElem_mem hi)

theorem prime_le_E {i : ℕ} (hi : i < d.m) : d.prime i ≤ d.E :=
  Nat.le_of_dvd d.E_pos (d.prime_dvd_E hi)

theorem E_div_prime_pos {i : ℕ} (hi : i < d.m) : 0 < d.E / d.prime i :=
  Nat.div_pos (d.prime_le_E hi) (d.prime_prime hi).pos

theorem E_div_prime_le (i : ℕ) : d.E / d.prime i ≤ d.E := Nat.div_le_self _ _

theorem two_mul_E_div_prime_le (i : ℕ) : 2 * (d.E / d.prime i) ≤ d.E :=
  (Nat.mul_le_mul_right _ (d.two_le_prime i)).trans (Nat.mul_div_le _ _)

/-- `E / ℓ_i ≤ E / 2`. -/
theorem E_div_prime_le_half (i : ℕ) : d.E / d.prime i ≤ d.E / 2 :=
  Nat.div_le_div_left (d.two_le_prime i) two_pos

theorem orderOf_ω : orderOf d.ω = d.E := d.hord

theorem orderOf_z {i : ℕ} (hi : i < d.m) : orderOf (d.z i) = d.prime i :=
  orderOf_pow_div d.orderOf_ω (d.prime_dvd_E hi) d.E_pos

theorem ω_ne_zero : d.ω ≠ 0 := by
  intro h
  have h1 := pow_orderOf_eq_one d.ω
  rw [d.orderOf_ω, h, zero_pow d.E_pos.ne'] at h1
  exact zero_ne_one h1

theorem isPrimitiveRoot_ω : IsPrimitiveRoot d.ω d.E := by
  rw [← d.orderOf_ω]
  exact IsPrimitiveRoot.orderOf d.ω

theorem E_dvd_p_sub_one : d.E ∣ d.p - 1 :=
  d.orderOf_ω ▸ ZMod.orderOf_dvd_card_sub_one d.ω_ne_zero

/-- `(p - 1 : ℕ)` is `-1` in `𝔽_p`. -/
theorem natCast_p_sub_one : ((d.p - 1 : ℕ) : ZMod d.p) = -1 := by
  rw [Nat.cast_sub d.hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-! ### Polynomials -/

/-- `R = X^E - 1`. -/
noncomputable def R : (ZMod d.p)[X] := X ^ d.E - 1

/-- `B_i = (X^{E/ℓ_i} - 1)(X^{E/ℓ_i} - z_i)`. -/
noncomputable def B (i : ℕ) : (ZMod d.p)[X] :=
  (X ^ (d.E / d.prime i) - 1) * (X ^ (d.E / d.prime i) - C (d.z i))

/-- Literal factor: `X^{E/ℓ_i} - z_i` for the positive literal, `X^{E/ℓ_i} - 1` for the negative. -/
noncomputable def litPoly (l : Lit) : (ZMod d.p)[X] :=
  X ^ (d.E / d.prime l.var) - C (if l.sign then d.z l.var else 1)

/-- Clause polynomial `P_C = ∏ L_λ`. -/
noncomputable def clausePoly (c : Clause) : (ZMod d.p)[X] := (c.map d.litPoly).prod

/-- The constraint list `[B_0, …, B_{m-1}, P_{C_1}, …, P_{C_k}]`. -/
noncomputable def constraintPolys (ψ : CNF) : List (ZMod d.p)[X] :=
  (List.range d.m).map d.B ++ ψ.map d.clausePoly

/-- `H = Σ_j u_j F_j` (list version; extra entries of either list are ignored). -/
noncomputable def Hpoly (us : List (ZMod d.p)) (Fs : List (ZMod d.p)[X]) : (ZMod d.p)[X] :=
  (List.zipWith (fun u F ↦ C u * F) us Fs).sum

/-! ### Sparse term lists -/

/-- `R` as terms: `X^E + (p-1)`. -/
def Rterms : Terms := [(1, d.E), (d.p - 1, 0)]

/-- Residue of a field element. -/
def val (a : ZMod d.p) : ℕ := a.val

/-- `B_i` as three terms: `X^{2E/ℓ_i} + (-(1+z_i)) X^{E/ℓ_i} + z_i`. -/
def Bterms (i : ℕ) : Terms :=
  [(1, 2 * (d.E / d.prime i)), (d.val (-(1 + d.z i)), d.E / d.prime i), (d.val (d.z i), 0)]

/-- Literal factor as two terms. -/
def litTerms (l : Lit) : Terms :=
  [(1, d.E / d.prime l.var), (d.val (-(if l.sign then d.z l.var else 1)), 0)]

/-- Product of term lists (all pairwise products, coefficients reduced mod `p`). -/
def mulTerms (p : ℕ) (l₁ l₂ : Terms) : Terms :=
  l₁.flatMap fun s ↦ l₂.map fun t ↦ ((s.1 * t.1) % p, s.2 + t.2)

/-- Clause polynomial as terms: product of the literal binomials (`≤ 2^{|C|}` terms). -/
def clauseTerms (c : Clause) : Terms := (c.map d.litTerms).foldr (mulTerms d.p) [(1, 0)]

/-- The constraint list as terms. -/
def constraintTerms (ψ : CNF) : List Terms :=
  (List.range d.m).map d.Bterms ++ ψ.map d.clauseTerms

/-- Scale a term list by `u` (coefficients reduced mod `p`). -/
def scaleTerms (p u : ℕ) (l : Terms) : Terms := l.map fun t ↦ ((u * t.1) % p, t.2)

/-- `H` as the concatenation of the scaled constraint lists. -/
def Hterms (p : ℕ) (us : List ℕ) (Fs : List Terms) : Terms :=
  (List.zipWith (scaleTerms p) us Fs).flatten

theorem clauseTerms_nil : d.clauseTerms [] = [(1, 0)] := rfl

theorem clauseTerms_cons (l : Lit) (c : Clause) :
    d.clauseTerms (l :: c) = mulTerms d.p (d.litTerms l) (d.clauseTerms c) := rfl

theorem mulTerms_cons (p : ℕ) (s : ℕ × ℕ) (l₁ l₂ : Terms) :
    mulTerms p (s :: l₁) l₂ = (l₂.map fun t ↦ ((s.1 * t.1) % p, s.2 + t.2)) ++ mulTerms p l₁ l₂ :=
  List.flatMap_cons

theorem Hterms_cons_cons (p u : ℕ) (us : List ℕ) (F : Terms) (Fs : List Terms) :
    Hterms p (u :: us) (F :: Fs) = scaleTerms p u F ++ Hterms p us Fs := rfl

/-- Every term of `mulTerms p l₁ l₂` is a product of a term of `l₁` and a term of `l₂`. -/
theorem exists_of_mem_mulTerms {p : ℕ} {l₁ l₂ : Terms} {t : ℕ × ℕ} (ht : t ∈ mulTerms p l₁ l₂) :
    ∃ s ∈ l₁, ∃ s' ∈ l₂, t = ((s.1 * s'.1) % p, s.2 + s'.2) := by
  simp only [mulTerms, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, s', hs', rfl⟩ := ht
  exact ⟨s, hs, s', hs', rfl⟩

/-- Every term of `Hterms p us Fs` is a scaled term of one of the `Fs`. -/
theorem exists_of_mem_Hterms {p : ℕ} {us : List ℕ} {Fs : List Terms} {t : ℕ × ℕ}
    (ht : t ∈ Hterms p us Fs) : ∃ u ∈ us, ∃ F ∈ Fs, ∃ s ∈ F, t = ((u * s.1) % p, s.2) := by
  induction us generalizing Fs with
  | nil => simp [Hterms] at ht
  | cons u us ih =>
    cases Fs with
    | nil => simp [Hterms] at ht
    | cons F Fs =>
      rw [Hterms_cons_cons, List.mem_append] at ht
      rcases ht with ht | ht
      · simp only [scaleTerms, List.mem_map] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        exact ⟨u, List.mem_cons_self .., F, List.mem_cons_self .., s, hs, rfl⟩
      · obtain ⟨u', hu', F', hF', s, hs, rfl⟩ := ih ht
        exact ⟨u', List.mem_cons_of_mem _ hu', F', List.mem_cons_of_mem _ hF', s, hs, rfl⟩

/-! ### Semantics of the term lists -/

theorem toPoly_Rterms : toPoly d.p d.Rterms = d.R := by
  simp only [Rterms, toPoly_cons, toPoly_nil, R, d.natCast_p_sub_one, Nat.cast_one, map_one,
    map_neg, pow_zero, mul_one, one_mul, add_zero, sub_eq_add_neg]

theorem toPoly_Bterms (i : ℕ) : toPoly d.p (d.Bterms i) = d.B i := by
  simp only [Bterms, toPoly_cons, toPoly_nil, val, ZMod.natCast_zmod_val, B, Nat.cast_one,
    map_one, map_neg, map_add, pow_zero, mul_one, one_mul, add_zero]
  ring

theorem toPoly_litTerms (l : Lit) : toPoly d.p (d.litTerms l) = d.litPoly l := by
  simp only [litTerms, toPoly_cons, toPoly_nil, val, ZMod.natCast_zmod_val, litPoly, Nat.cast_one,
    map_one, map_neg, pow_zero, mul_one, one_mul, add_zero, sub_eq_add_neg]

private theorem toPoly_map_mul (p : ℕ) (s : ℕ × ℕ) (l : Terms) :
    toPoly p (l.map fun t ↦ ((s.1 * t.1) % p, s.2 + t.2)) =
      C (s.1 : ZMod p) * X ^ s.2 * toPoly p l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPoly_cons, ih, ZMod.natCast_mod, Nat.cast_mul, C_mul, pow_add]
    ring

theorem toPoly_mulTerms (p : ℕ) (l₁ l₂ : Terms) :
    toPoly p (mulTerms p l₁ l₂) = toPoly p l₁ * toPoly p l₂ := by
  induction l₁ with
  | nil => simp [mulTerms]
  | cons s l₁ ih =>
    rw [mulTerms_cons, toPoly_append, toPoly_map_mul, ih, toPoly_cons, add_mul]

theorem toPoly_clauseTerms (c : Clause) : toPoly d.p (d.clauseTerms c) = d.clausePoly c := by
  induction c with
  | nil => simp [clauseTerms_nil, clausePoly]
  | cons l c ih =>
    rw [clauseTerms_cons, toPoly_mulTerms, ih, toPoly_litTerms, clausePoly, clausePoly,
      List.map_cons, List.prod_cons]

theorem toPoly_constraintTerms (ψ : CNF) :
    (d.constraintTerms ψ).map (toPoly d.p) = d.constraintPolys ψ := by
  simp only [constraintTerms, constraintPolys, List.map_append, List.map_map, Function.comp_def,
    d.toPoly_Bterms, d.toPoly_clauseTerms]

theorem toPoly_scaleTerms (p u : ℕ) (l : Terms) :
    toPoly p (scaleTerms p u l) = C (u : ZMod p) * toPoly p l := by
  induction l with
  | nil => simp [scaleTerms]
  | cons t l ih =>
    simp only [scaleTerms, List.map_cons, toPoly_cons, ZMod.natCast_mod, Nat.cast_mul, C_mul,
      mul_add, mul_assoc] at ih ⊢
    rw [ih]

private theorem toPoly_flatten (p : ℕ) (L : List Terms) :
    toPoly p L.flatten = (L.map (toPoly p)).sum := by
  induction L with
  | nil => simp
  | cons l L ih => rw [List.flatten_cons, toPoly_append, ih, List.map_cons, List.sum_cons]

theorem toPoly_Hterms (p : ℕ) (us : List ℕ) (Fs : List Terms) :
    toPoly p (Hterms p us Fs) =
      (List.zipWith (fun (u : ℕ) F ↦ C (u : ZMod p) * toPoly p F) us Fs).sum := by
  rw [Hterms, toPoly_flatten, List.map_zipWith]
  simp only [toPoly_scaleTerms]

theorem toPoly_Hterms_eq_Hpoly (us : List ℕ) (ψ : CNF) :
    toPoly d.p (Hterms d.p us (d.constraintTerms ψ)) =
      d.Hpoly (us.map fun u : ℕ ↦ (u : ZMod d.p)) (d.constraintPolys ψ) := by
  rw [toPoly_Hterms, Hpoly, ← toPoly_constraintTerms, List.zipWith_map]

/-! ### Bounds (Lemma 25) -/

theorem length_Rterms : d.Rterms.length = 2 := rfl

theorem length_Bterms (i : ℕ) : (d.Bterms i).length = 3 := rfl

theorem length_litTerms (l : Lit) : (d.litTerms l).length = 2 := rfl

theorem length_mulTerms (p : ℕ) (l₁ l₂ : Terms) :
    (mulTerms p l₁ l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp [mulTerms]
  | cons s l₁ ih =>
    rw [mulTerms_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

theorem length_clauseTerms (c : Clause) : (d.clauseTerms c).length = 2 ^ c.length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rw [clauseTerms_cons, length_mulTerms, ih, length_litTerms, List.length_cons, pow_succ,
      mul_comm]

theorem length_clauseTerms_le {c : Clause} (hc : c.length ≤ 3) : (d.clauseTerms c).length ≤ 8 := by
  rw [length_clauseTerms]
  exact (Nat.pow_le_pow_right two_pos hc).trans (by norm_num)

theorem length_scaleTerms (p u : ℕ) (l : Terms) : (scaleTerms p u l).length = l.length :=
  List.length_map ..

/-- `|H|` is at most the total length of the constraint lists. -/
theorem length_Hterms_le_sum (p : ℕ) (us : List ℕ) (Fs : List Terms) :
    (Hterms p us Fs).length ≤ (Fs.map List.length).sum := by
  induction us generalizing Fs with
  | nil => simp [Hterms]
  | cons u us ih =>
    cases Fs with
    | nil => simp [Hterms]
    | cons F Fs =>
      rw [Hterms_cons_cons, List.length_append, length_scaleTerms, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih Fs) _

private theorem sum_length_clauseTerms_le {ψ : CNF} (hψ : BoundedClauses ψ) :
    (ψ.map fun c ↦ (d.clauseTerms c).length).sum ≤ 8 * ψ.length := by
  induction ψ with
  | nil => simp
  | cons c ψ ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := d.length_clauseTerms_le (hψ c (List.mem_cons_self ..))
    have h2 := ih fun c' hc' ↦ hψ c' (List.mem_cons_of_mem _ hc')
    omega

/-- `|H| ≤ 3m + 8k` for a bounded-clause formula with `k` clauses. -/
theorem length_Hterms_le {ψ : CNF} (hψ : BoundedClauses ψ) (us : List ℕ) :
    (Hterms d.p us (d.constraintTerms ψ)).length ≤ 3 * d.m + 8 * ψ.length := by
  refine (length_Hterms_le_sum _ _ _).trans ?_
  rw [constraintTerms, List.map_append, List.sum_append, List.map_map, List.map_map]
  have h1 : ((List.range d.m).map (List.length ∘ d.Bterms)).sum = 3 * d.m := by
    simp [Function.comp_def, length_Bterms, List.map_const', mul_comm]
  have h2 := d.sum_length_clauseTerms_le hψ
  simp only [Function.comp_def] at h1 h2 ⊢
  omega

theorem constraintTerms_length (ψ : CNF) : (d.constraintTerms ψ).length = d.m + ψ.length := by
  simp [constraintTerms]

/-- Coefficients are reduced. -/
theorem wf_Rterms : WFTerms d.p d.Rterms := by
  have := d.hp.two_le
  simp only [WFTerms, Rterms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  omega

theorem wf_Bterms (i : ℕ) : WFTerms d.p (d.Bterms i) := by
  intro t ht
  simp only [Bterms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact d.hp.one_lt
  · exact ZMod.val_lt _
  · exact ZMod.val_lt _

theorem wf_mulTerms {p : ℕ} (hp : 0 < p) (l₁ l₂ : Terms) : WFTerms p (mulTerms p l₁ l₂) := by
  intro t ht
  obtain ⟨s, -, s', -, rfl⟩ := exists_of_mem_mulTerms ht
  exact Nat.mod_lt _ hp

theorem wf_clauseTerms (c : Clause) : WFTerms d.p (d.clauseTerms c) := by
  cases c with
  | nil =>
    intro t ht
    rw [clauseTerms_nil, List.mem_singleton] at ht
    rw [ht]
    exact d.hp.one_lt
  | cons l c =>
    rw [clauseTerms_cons]
    exact wf_mulTerms d.hp.pos _ _

theorem wf_Hterms (us : List ℕ) (Fs : List Terms) : WFTerms d.p (Hterms d.p us Fs) := by
  intro t ht
  obtain ⟨u, -, F, -, s, -, rfl⟩ := exists_of_mem_Hterms ht
  exact Nat.mod_lt _ d.hp.pos

/-- Exponents of `B_i` are at most `E`. -/
theorem exponent_Bterms_le (i : ℕ) : ∀ t ∈ d.Bterms i, t.2 ≤ d.E := by
  intro t ht
  simp only [Bterms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact d.two_mul_E_div_prime_le i
  · exact d.E_div_prime_le i
  · exact Nat.zero_le _

/-- Exponents of `litTerms` are at most `E / 2`. -/
theorem exponent_litTerms_le (l : Lit) : ∀ t ∈ d.litTerms l, t.2 ≤ d.E / 2 := by
  intro t ht
  simp only [litTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact d.E_div_prime_le_half _
  · exact Nat.zero_le _

/-- Exponents of a product of term lists add up. -/
theorem exponent_mulTerms_le {p D₁ D₂ : ℕ} {l₁ l₂ : Terms} (h₁ : ∀ t ∈ l₁, t.2 ≤ D₁)
    (h₂ : ∀ t ∈ l₂, t.2 ≤ D₂) : ∀ t ∈ mulTerms p l₁ l₂, t.2 ≤ D₁ + D₂ := by
  intro t ht
  obtain ⟨s, hs, s', hs', rfl⟩ := exists_of_mem_mulTerms ht
  exact Nat.add_le_add (h₁ s hs) (h₂ s' hs')

/-- Exponents of a clause polynomial with `k` literals are at most `k · (E / 2)`. -/
theorem exponent_clauseTerms_le_mul (c : Clause) :
    ∀ t ∈ d.clauseTerms c, t.2 ≤ c.length * (d.E / 2) := by
  induction c with
  | nil =>
    intro t ht
    rw [clauseTerms_nil, List.mem_singleton] at ht
    rw [ht]
    exact Nat.zero_le _
  | cons l c ih =>
    intro t ht
    rw [clauseTerms_cons] at ht
    have := exponent_mulTerms_le (d.exponent_litTerms_le l) ih t ht
    rw [List.length_cons, add_mul, one_mul, add_comm]
    exact this

/-- Exponents of a clause polynomial with at most three literals are at most `2E`. -/
theorem exponent_clauseTerms_le {c : Clause} (hc : c.length ≤ 3) :
    ∀ t ∈ d.clauseTerms c, t.2 ≤ 2 * d.E := by
  intro t ht
  have h1 := d.exponent_clauseTerms_le_mul c t ht
  have h2 : c.length * (d.E / 2) ≤ 3 * (d.E / 2) := Nat.mul_le_mul_right _ hc
  omega

theorem exponent_Hterms_le {ψ : CNF} (hψ : BoundedClauses ψ) (us : List ℕ) :
    ∀ t ∈ Hterms d.p us (d.constraintTerms ψ), t.2 ≤ 2 * d.E := by
  intro t ht
  obtain ⟨u, -, F, hF, s, hs, rfl⟩ := exists_of_mem_Hterms ht
  show s.2 ≤ 2 * d.E
  simp only [constraintTerms, List.mem_append, List.mem_map, List.mem_range] at hF
  rcases hF with ⟨i, -, rfl⟩ | ⟨c, hc, rfl⟩
  · exact (d.exponent_Bterms_le i s hs).trans (by omega)
  · exact d.exponent_clauseTerms_le (hψ c hc) s hs

theorem natDegree_toPoly_le_of_exponent_le {p D : ℕ} {l : Terms} (h : ∀ t ∈ l, t.2 ≤ D) :
    (toPoly p l).natDegree ≤ D := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [toPoly_cons]
    refine (natDegree_add_le _ _).trans
      (max_le ?_ (ih fun s hs ↦ h s (List.mem_cons_of_mem _ hs)))
    exact (natDegree_C_mul_X_pow_le _ _).trans (h t (List.mem_cons_self ..))

theorem natDegree_R : d.R.natDegree = d.E := by
  rw [R, ← C_1, natDegree_X_pow_sub_C]

theorem R_ne_zero : d.R ≠ 0 := by
  rw [R, ← C_1]
  exact X_pow_sub_C_ne_zero d.E_pos 1

theorem natDegree_Hpoly_le {ψ : CNF} (hψ : BoundedClauses ψ) (us : List ℕ) :
    (d.Hpoly (us.map fun u : ℕ ↦ (u : ZMod d.p)) (d.constraintPolys ψ)).natDegree ≤ 2 * d.E := by
  rw [← toPoly_Hterms_eq_Hpoly]
  exact natDegree_toPoly_le_of_exponent_le (d.exponent_Hterms_le hψ us)

/-- `R` has exactly two terms after normalization (`p ≥ 2`, `E ≥ 1`). -/
theorem normalized_Rterms : Normalized d.p [(d.p - 1, 0), (1, d.E)] := by
  have h2 := d.hp.two_le
  have hE := d.E_pos
  refine ⟨?_, ?_⟩
  · simp [hE]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega

theorem toPoly_Rterms' : toPoly d.p [(d.p - 1, 0), (1, d.E)] = d.R := by
  rw [← d.toPoly_Rterms]
  simp only [Rterms, toPoly_cons, toPoly_nil]
  ring

end RootData

end SparseGcd
