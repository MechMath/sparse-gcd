import SparseGcd.Machine.TrialData

/-!
# Correctness facts about the stages of a trial

* From a valid package and a residue `w` passing the order test we build the `RootData` used by
  the mathematical lemmas (`rootDataOf`), and show the raw (`ℕ`-arithmetic) term lists coincide
  with the `RootData` ones.
* Size bounds: `m ≤ Vmax s`, `k ≤ Kmax s`, `E < p`, `bitLength p ≤ Bb - 1`, instance length
  `≤ Zmax`, the constructed instance is well formed, and on the success event the gcd has at most
  two terms (the promise of the output-sensitive solver).
-/

open Complexity SAT SparseDiv Polynomial Finset

namespace SparseGcd

/-! ### From residues to `ZMod p` -/

theorem natCast_powMod (p : ℕ) [NeZero p] (b e : ℕ) : ((powMod b e p : ℕ) : ZMod p) = (b : ZMod p) ^ e := by
  rw [powMod, ZMod.natCast_mod, Nat.cast_pow]

/-- The order test on residues is the order test in `ZMod p`. -/
theorem orderTestNat_iff (p E : ℕ) (hp : 2 ≤ p) (ℓ : List ℕ) (w : ℕ) :
    orderTestNat p E ℓ w = true ↔ OrderTest (p := p) E ℓ (w : ZMod p) := by
  have : NeZero p := ⟨by omega⟩
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have key : ∀ x : ℕ, ((x : ℕ) : ZMod p) = 1 ↔ x % p = 1 := fun x ↦ by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h1]
  have key2 : ∀ b e : ℕ, (powMod b e p = 1 ↔ (b : ZMod p) ^ e = 1) := fun b e ↦ by
    rw [← natCast_powMod, key, powMod, Nat.mod_mod]
  simp only [orderTestNat, OrderTest, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne,
    ne_eq, h1, key2]

/-- `findOmega` returns a residue passing the order test. -/
theorem findOmega_some {p E : ℕ} {ℓ : List ℕ} {t B : ℕ} {bits : List Bool} {w : ℕ}
    (h : findOmega p E ℓ t B bits = some w) (hp : 0 < p) :
    w < p ∧ orderTestNat p E ℓ w = true := by
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  simp only at hi
  split_ifs at hi with hw
  simp only [Option.some.injEq] at hi
  subst hi
  exact ⟨Nat.mod_lt _ hp, hw⟩

/-- The `RootData` of a valid package restricted to `m` primes and a residue `w` of exact order. -/
def rootDataOf {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c) (m : ℕ) {w : ℕ}
    (hw : w < 1 + c * ℓ.prod)
    (hord : orderOf (w : ZMod (1 + c * ℓ.prod)) = (ℓ.take m).prod) : RootData :=
  ⟨1 + c * ℓ.prod, hv.2.2.2.2, ℓ.take m, fun q hq ↦ hv.2.2.1 q (List.mem_of_mem_take hq),
    hv.2.1.sublist (List.take_sublist _ _), w, hw, hord⟩

theorem orderOf_of_orderTestNat {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c) (m : ℕ)
    {w : ℕ} (h : orderTestNat (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) w = true) :
    orderOf (w : ZMod (1 + c * ℓ.prod)) = (ℓ.take m).prod := by
  rw [orderOf_eq_iff_orderTest (fun q hq ↦ hv.2.2.1 q (List.mem_of_mem_take hq))
    (hv.2.1.sublist (List.take_sublist _ _))]
  exact (orderTestNat_iff _ _ hv.2.2.2.2.two_le _ _).mp h

/-! ### Raw term lists agree with the `RootData` ones -/

theorem rootDataOf_p {N ℓ c} (hv : ValidPackage N ℓ c) (m) {w} (hw) (hord) :
    (rootDataOf hv m (w := w) hw hord).p = 1 + c * ℓ.prod := rfl

theorem rootDataOf_ℓ {N ℓ c} (hv : ValidPackage N ℓ c) (m) {w} (hw) (hord) :
    (rootDataOf hv m (w := w) hw hord).ℓ = ℓ.take m := rfl

theorem rootDataOf_m {N ℓ c} (hv : ValidPackage N ℓ c) (m) (hm : m ≤ N) {w} (hw) (hord) :
    (rootDataOf hv m (w := w) hw hord).m = m := by
  show (ℓ.take m).length = m
  rw [List.length_take]
  exact Nat.min_eq_left (hm.trans hv.1.symm.le)

/-- `((w : ZMod p) ^ e).val = w ^ e % p`. -/
private theorem val_natCast_pow (p w e : ℕ) : ((w : ZMod p) ^ e).val = w ^ e % p := by
  rw [← Nat.cast_pow, ZMod.val_natCast]

theorem rawBterms_eq (d : RootData) (i : ℕ) : rawBterms d.p d.E d.ℓ d.w i = d.Bterms i := by
  simp only [rawBterms, RootData.Bterms, RootData.val, RootData.z, RootData.ω, RootData.prime,
    powMod]
  rw [ZMod.neg_val', ZMod.val_add, ZMod.val_one_eq_one_mod, val_natCast_pow,
    Nat.mod_eq_of_lt d.hp.one_lt]

theorem rawLitTerms_eq (d : RootData) (l : Lit) : rawLitTerms d.p d.E d.ℓ d.w l = d.litTerms l := by
  simp only [rawLitTerms, RootData.litTerms, RootData.val, RootData.z, RootData.ω, RootData.prime,
    powMod]
  rw [ZMod.neg_val']
  by_cases hs : l.sign = true
  · simp only [hs, ite_true, val_natCast_pow, Nat.mod_mod]
  · simp only [hs, Bool.false_eq_true, ite_false, ZMod.val_one_eq_one_mod]

theorem rawClauseTerms_eq (d : RootData) (c : Clause) :
    rawClauseTerms d.p d.E d.ℓ d.w c = d.clauseTerms c := by
  have h : rawLitTerms d.p d.E d.ℓ d.w = d.litTerms := funext (rawLitTerms_eq d)
  simp only [rawClauseTerms, RootData.clauseTerms, h]

theorem rawConstraintTerms_eq (d : RootData) (ψ : CNF) :
    rawConstraintTerms d.p d.E d.ℓ d.w d.m ψ = d.constraintTerms ψ := by
  have h1 : rawBterms d.p d.E d.ℓ d.w = d.Bterms := funext (rawBterms_eq d)
  have h2 : rawClauseTerms d.p d.E d.ℓ d.w = d.clauseTerms := funext (rawClauseTerms_eq d)
  simp only [rawConstraintTerms, RootData.constraintTerms, h1, h2]

theorem toPoly_rawRterms (d : RootData) : toPoly d.p (rawRterms d.p d.E) = d.R :=
  d.toPoly_Rterms'

theorem normalized_rawRterms (d : RootData) : Normalized d.p (rawRterms d.p d.E) :=
  d.normalized_Rterms

theorem toPoly_buildH (d : RootData) (ψ : CNF) (B : ℕ) (bits : List Bool) :
    toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ B bits) =
      toPoly d.p (RootData.Hterms d.p (coeffs d.p B (d.m + ψ.length) bits) (d.constraintTerms ψ)) := by
  rw [buildH, rawConstraintTerms_eq, toPoly_normalize]

theorem buildH_eq (d : RootData) (ψ : CNF) (B : ℕ) (bits : List Bool) :
    buildH d.p d.E d.ℓ d.w d.m ψ B bits =
      normalize d.p (RootData.Hterms d.p (coeffs d.p B (d.m + ψ.length) bits) (d.constraintTerms ψ)) := by
  rw [buildH, rawConstraintTerms_eq]

theorem normalized_buildH (d : RootData) (ψ : CNF) (B : ℕ) (bits : List Bool) :
    Normalized d.p (buildH d.p d.E d.ℓ d.w d.m ψ B bits) := by
  rw [buildH]
  exact normalized_normalize d.hp.pos _

theorem coeffs_lt (p B t : ℕ) (hp : 0 < p) (bits : List Bool) : ∀ u ∈ coeffs p B t bits, u < p := by
  intro u hu
  simp only [coeffs, List.mem_map] at hu
  obtain ⟨i, -, rfl⟩ := hu
  exact Nat.mod_lt _ hp

theorem length_coeffs (p B t : ℕ) (bits : List Bool) : (coeffs p B t bits).length = t := by
  simp [coeffs]

/-! ### Well-formedness of the produced instance -/

theorem wfGcd_instance (d : RootData) (H : Terms) (hH : Normalized d.p H) :
    WFGcd d.p (rawRterms d.p d.E) H :=
  ⟨d.hp, normalized_rawRterms d, hH⟩

theorem wfRou_instance (d : RootData) (H : Terms) (hH : Normalized d.p H) :
    WFRou d.p H d.E :=
  ⟨d.hp, hH, d.E_pos⟩

set_option linter.unusedVariables false in
/-- On the success event the gcd has at most two terms (`hH` is kept for the uniform interface). -/
theorem length_gcdTerms_le_two (d : RootData) {ψ : CNF} (hψ : CNF.VarsLt ψ d.m)
    (hcard : (solutions ψ d.m).card ≤ 1) {H : Terms} (hH : Normalized d.p H)
    (hZ : d.commonZeros [toPoly d.p H] = d.commonZeros (d.constraintPolys ψ)) :
    (gcdTerms d.p (rawRterms d.p d.E) H).length ≤ 2 := by
  rw [gcdTerms, toPoly_rawRterms]
  exact d.length_termsOf_monicGcd_of_success hψ hZ hcard

/-- The degree test on the canonical gcd output. -/
theorem exists_pos_exponent_gcdTerms_iff (d : RootData) (H : Terms) :
    (∃ t ∈ gcdTerms d.p (rawRterms d.p d.E) H, 0 < t.2) ↔
      0 < (monicGcd d.R (toPoly d.p H)).natDegree := by
  rw [gcdTerms, toPoly_rawRterms]
  simp only [termsOf, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨t, ⟨e, he, rfl⟩, ht⟩
    exact lt_of_lt_of_le ht (le_natDegree_of_mem_supp e he)
  · intro hg
    refine ⟨_, ⟨(monicGcd d.R (toPoly d.p H)).natDegree, ?_, rfl⟩, hg⟩
    exact natDegree_mem_support_of_nonzero fun h ↦ by simp [h] at hg

/-- Roots-of-unity membership of the produced instance. -/
theorem mem_RootsOfUnity_iff (d : RootData) (H : Terms) (hH : Normalized d.p H) :
    encRouInstance d.p H d.E ∈ RootsOfUnity ↔ 0 < (monicGcd d.R (toPoly d.p H)).natDegree := by
  rw [mem_RootsOfUnity_encRouInstance_iff, and_iff_right (wfRou_instance d H hH)]
  have hR : (X ^ d.E - 1 : (ZMod d.p)[X]) = d.R := rfl
  rw [hR, not_isCoprime_iff_natDegree_monicGcd_pos (Or.inr d.R_ne_zero), monicGcd_comm]

theorem mem_rouPromise_promise (d : RootData) (H : Terms) (hH : Normalized d.p H) :
    encRouInstance d.p H d.E ∈ rouPromise.promise := by
  rw [rouPromise_promise]
  exact ⟨d.p, H, d.E, decRouInstance_encRouInstance _ _ _, wfRou_instance d H hH⟩

/-! ### Size bounds -/

theorem isolateSeed_snd_le_Vmax {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s) (kb hb : List Bool) :
    (isolateSeed φ kb hb).2 ≤ Vmax s := by
  have h := isolateSeed_snd_le φ kb hb
  have h1 := maxVar_le_length_encode φ
  have h2 := numLits_le_length_encode φ
  rw [hs] at h1 h2
  have h3 : (φ.maxVar + 3) * (φ.maxVar + 1) ≤ (s + 3) * (s + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold Vmax
  omega

theorem isolateSeed_length_le_Kmax {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s) (kb hb : List Bool) :
    (isolateSeed φ kb hb).1.length ≤ Kmax s := by
  have h := isolateSeed_length_le φ kb hb
  have h1 := maxVar_le_length_encode φ
  have h2 := numLits_le_length_encode φ
  have h4 := length_le_length_encode φ
  rw [hs] at h1 h2 h4
  have h3 : (φ.maxVar + 3) * (4 * (φ.maxVar + 1) + 1) ≤ (s + 3) * (4 * (s + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold Kmax
  omega

theorem maxVar_succ_le {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s) : φ.maxVar + 1 ≤ s + 1 := by
  have := maxVar_le_length_encode φ
  omega

theorem kBits_le_KB {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s) : kBits (φ.maxVar + 1) ≤ KB s := by
  have := maxVar_succ_le hs
  unfold KB kBits
  exact Nat.size_le_size (by omega)

theorem hashBits_le_HB {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s) :
    hashBits (φ.maxVar + 1) ≤ HB s := by
  have := maxVar_succ_le hs
  unfold HB hashBits
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `2^cnt > 400 r`. -/
theorem lt_two_pow_cnt (s : ℕ) : 400 * r s < 2 ^ cnt s :=
  Nat.lt_size_self _

theorem four_le_Nn (s : ℕ) : 4 ≤ Nn s := by
  unfold Nn
  omega

/-- `E / p ≤ 2^{-(N - m)} ≤ 2^{-cnt}` for `m ≤ Vmax`. -/
theorem E_div_p_le_of_le {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c) {m s : ℕ}
    (hN : N = Nn s) (hm : m ≤ Vmax s) :
    ((ℓ.take m).prod : ℚ) / (1 + c * ℓ.prod) ≤ 1 / 2 ^ cnt s := by
  have hlen : ℓ.length = Vmax s + cnt s + 4 := by rw [hv.1, hN]; rfl
  have hmN : m ≤ hv.toPackage.N := by
    show m ≤ ℓ.length
    omega
  have h := hv.toPackage.E_div_p_le hmN
  have e1 : (hv.toPackage.E m : ℚ) = ((ℓ.take m).prod : ℚ) := rfl
  have e2 : (hv.toPackage.p : ℚ) = ((1 + c * ℓ.prod : ℕ) : ℚ) := rfl
  rw [e1, e2, Nat.cast_add, Nat.cast_one, Nat.cast_mul] at h
  refine h.trans ?_
  have hle : cnt s ≤ hv.toPackage.N - m := by
    show cnt s ≤ ℓ.length - m
    omega
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hle)

/-- `2 p ≤ 2^Bb` for a package of the construction. -/
theorem two_mul_p_le_two_pow_Bb (C : PrimeConstruction) {s : ℕ} {ℓ : List ℕ} {c : ℕ}
    (hb : Nat.size (1 + c * ℓ.prod) ≤ C.bitBound.eval (Nn s)) :
    2 * (1 + c * ℓ.prod) ≤ 2 ^ C.Bb s := by
  have h1 := Nat.lt_size_self (1 + c * ℓ.prod)
  have h2 : 2 ^ Nat.size (1 + c * ℓ.prod) ≤ 2 ^ C.bitBound.eval (Nn s) :=
    Nat.pow_le_pow_right two_pos hb
  rw [PrimeConstruction.Bb, pow_succ]
  omega

/-- Every exponent of `buildH` is at most `2E`. -/
private theorem exponent_buildH_le (d : RootData) {ψ : CNF} (hψ : BoundedClauses ψ) (B : ℕ)
    (bits : List Bool) : ∀ t ∈ buildH d.p d.E d.ℓ d.w d.m ψ B bits, t.2 ≤ 2 * d.E := by
  intro t ht
  have h1 := exponent_le_natDegree_of_normalized (normalized_buildH d ψ B bits) ht
  rw [toPoly_buildH] at h1
  exact h1.trans (RootData.natDegree_toPoly_le_of_exponent_le (d.exponent_Hterms_le hψ _))

/-- Number of terms of `buildH`. -/
private theorem length_buildH_le (d : RootData) {ψ : CNF} (hψ : BoundedClauses ψ) (B : ℕ)
    (bits : List Bool) : (buildH d.p d.E d.ℓ d.w d.m ψ B bits).length ≤ 3 * d.m + 8 * ψ.length := by
  rw [buildH_eq]
  exact (length_normalize_le _ _).trans (d.length_Hterms_le hψ _)

/-- Bit-length bound of a term list with coefficients and exponents of at most `b` bits. -/
private theorem length_encTerms_le_of_size_le {l : Terms} {b : ℕ}
    (hc : ∀ t ∈ l, Nat.size t.1 ≤ b) (he : ∀ t ∈ l, Nat.size t.2 ≤ b) :
    (encTerms l).length ≤ l.length * (8 * (b + 4)) := by
  rw [length_encTerms]
  have h := List.sum_le_length_nsmul (l.map fun t ↦ 2 * (encTerm t).length + 2) (8 * (b + 4)) ?_
  · rw [List.length_map, smul_eq_mul] at h
    exact h
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [length_encTerm]
    have := hc t ht
    have := he t ht
    omega

/-- Length of the encoded instance. -/
theorem length_encDivInstance_le (C : PrimeConstruction) {s : ℕ} (d : RootData)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s) {ψ : CNF}
    (hψ : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s) (B : ℕ) (bits : List Bool) :
    (encDivInstance d.p (rawRterms d.p d.E) (buildH d.p d.E d.ℓ d.w d.m ψ B bits)).length ≤
      (C.Zmax s - 4) / 4 := by
  have hBb : C.Bb s = C.bitBound.eval (Nn s) + 1 := rfl
  have hp1 : 1 < d.p := d.hp.one_lt
  have hsp : Nat.size d.p ≤ C.Bb s := by omega
  -- `2 p ≤ 2 ^ Bb`
  have h2p : 2 * d.p ≤ 2 ^ C.Bb s := by
    have h1 := Nat.lt_size_self d.p
    have h2 : 2 ^ Nat.size d.p ≤ 2 ^ C.bitBound.eval (Nn s) := Nat.pow_le_pow_right two_pos hp
    rw [hBb, pow_succ]
    omega
  have hE : d.E ≤ d.p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp1) d.E_dvd_p_sub_one
  have hsE : Nat.size d.E ≤ C.Bb s := (Nat.size_le_size (by omega)).trans hsp
  have hsp1 : Nat.size (d.p - 1) ≤ C.Bb s := (Nat.size_le_size (by omega)).trans hsp
  -- the `R` part
  have hR : (encTerms (rawRterms d.p d.E)).length ≤ 8 * (C.Bb s + 4) := by
    simp only [rawRterms, length_encTerms, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, length_encTerm, Nat.size_zero, Nat.size_one]
    omega
  -- the `H` part
  have hHn := normalized_buildH d ψ B bits
  have hHc : ∀ t ∈ buildH d.p d.E d.ℓ d.w d.m ψ B bits, Nat.size t.1 ≤ C.Bb s := fun t ht ↦
    (Nat.size_le_size (hHn.2 t ht).2.le).trans hsp
  have hHe : ∀ t ∈ buildH d.p d.E d.ℓ d.w d.m ψ B bits, Nat.size t.2 ≤ C.Bb s := fun t ht ↦ by
    have := exponent_buildH_le d hψ B bits t ht
    exact Nat.size_le.mpr (by omega)
  have hHlen : (buildH d.p d.E d.ℓ d.w d.m ψ B bits).length ≤ 3 * Vmax s + 8 * Kmax s := by
    have := length_buildH_le d hψ B bits
    omega
  have hHenc : (encTerms (buildH d.p d.E d.ℓ d.w d.m ψ B bits)).length ≤
      (3 * Vmax s + 8 * Kmax s) * (8 * (C.Bb s + 4)) :=
    (length_encTerms_le_of_size_le hHc hHe).trans (Nat.mul_le_mul_right _ hHlen)
  -- assemble
  have hZ : (C.Zmax s - 4) / 4 = 2 * C.Bb s + 2 +
      (2 * (8 * (C.Bb s + 4)) + 2 + (3 * Vmax s + 8 * Kmax s) * (8 * (C.Bb s + 4))) := by
    rw [PrimeConstruction.Zmax]
    omega
  rw [hZ, length_encDivInstance]
  omega

theorem length_inst_le (Or : DegreeOracle) (C : PrimeConstruction) {s : ℕ} (d : RootData)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s) {ψ : CNF}
    (hψ : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s) (B : ℕ) (bits : List Bool) :
    (Or.inst d.p (rawRterms d.p d.E) (buildH d.p d.E d.ℓ d.w d.m ψ B bits)).length ≤ C.Zmax s := by
  have h1 := Or.inst_length_le d.p (rawRterms d.p d.E) (buildH d.p d.E d.ℓ d.w d.m ψ B bits)
  have h2 := length_encDivInstance_le C d hp hm hψ hk B bits
  have h3 : 4 * ((C.Zmax s - 4) / 4) + 4 = C.Zmax s := by
    rw [PrimeConstruction.Zmax]
    omega
  omega

end SparseGcd
