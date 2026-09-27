import SparseGcd.Machine.StageLemmas

/-!
# Probabilities of the two sampling stages

* **ω-search** (Lemma 15/22): each attempt succeeds with probability `≥ 1/(4(m+1))` (density of
  good bases `≥ (p-1)/(m+1)` times the near-uniformity `1/p - 2^{-B} ≥ 1/(2p)`), attempts are
  independent blocks, so all `t` attempts fail with probability `≤ (1 - 1/(4(m+1)))^t`.
* **Compression** (Lemma 17/24): for every root `α` of `R` that is not a common zero of the
  constraints, exactly one residue of the distinguished coefficient makes `H(α) = 0`; that
  residue has probability `≤ 1/p + 2^{-B} ≤ 2/p` whatever the other blocks are; a union bound over
  the `E` roots gives `Pr[Z(R,H) ≠ Z(R,F)] ≤ 2E/p`.
-/

open Complexity SAT SparseDiv Polynomial Finset

namespace SparseGcd

/-- One ω attempt succeeds. -/
def omegaGood (p E : ℕ) (ℓ : List ℕ) (B : ℕ) : Finset (BitString B) :=
  univ.filter fun v ↦ orderTestNat p E ℓ (powMod (decNat (List.ofFn v) % p) ((p - 1) / E) p) = true

/-- The order test on `a^{(p-1)/E}` (computed on residues) is membership of `a` in `goodBases`. -/
private theorem orderTestNat_powMod_iff {p : ℕ} [Fact p.Prime] {ℓ : List ℕ}
    (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) (a : ℕ) :
    orderTestNat p ℓ.prod ℓ (powMod (a % p) ((p - 1) / ℓ.prod) p) = true ↔
      (a : ZMod p) ∈ goodBases p ℓ.prod := by
  rw [orderTestNat_iff p _ (Fact.out : p.Prime).two_le, natCast_powMod, ZMod.natCast_mod,
    ← orderOf_eq_iff_orderTest hprime hnodup, goodBases, mem_filter]
  simp

/-- `a mod p` lies in the image of `G` under `val` iff `(a : ZMod p) ∈ G`. -/
private theorem mod_mem_image_val_iff {p : ℕ} [NeZero p] (G : Finset (ZMod p)) (a : ℕ) :
    a % p ∈ G.image ZMod.val ↔ (a : ZMod p) ∈ G := by
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rwa [← ZMod.natCast_mod, ← hxa, ZMod.natCast_zmod_val]
  · intro h
    exact ⟨_, h, ZMod.val_natCast p a⟩

theorem eventProb_omegaGood_ge {p : ℕ} [Fact p.Prime] {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime)
    (hnodup : ℓ.Nodup) (hE : ℓ.prod ∣ p - 1) {B : ℕ} (hB : 2 * p ≤ 2 ^ B) :
    (1 : ℚ) / (4 * (ℓ.length + 1)) ≤ eventProb (omegaGood p ℓ.prod ℓ B) := by
  classical
  set S : Finset ℕ := (goodBases p ℓ.prod).image ZMod.val with hSdef
  have hS : ∀ r ∈ S, r < p := by
    intro r hr
    obtain ⟨x, -, rfl⟩ := mem_image.1 hr
    exact ZMod.val_lt x
  have hScard : S.card = (goodBases p ℓ.prod).card :=
    card_image_of_injective _ (ZMod.val_injective p)
  have heq : omegaGood p ℓ.prod ℓ B = univ.filter fun v : BitString B ↦ bitsVal v % p ∈ S := by
    ext v
    simp only [omegaGood, mem_filter, mem_univ, true_and, hSdef, bitsVal]
    rw [orderTestNat_powMod_iff hprime hnodup, mod_mem_image_val_iff]
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hB' : (2 : ℚ) * p ≤ 2 ^ B := by exact_mod_cast hB
  have hx : 1 / (2 * (p : ℚ)) ≤ 1 / p - 1 / 2 ^ B := by
    have h1 : (1 : ℚ) / 2 ^ B ≤ 1 / (2 * p) := one_div_le_one_div_of_le (by positivity) hB'
    have h2 : (1 : ℚ) / p - 1 / (2 * p) = 1 / (2 * p) := by field_simp; ring
    linarith
  have hcardS : ((p : ℚ) - 1) / (ℓ.length + 1) ≤ S.card := by
    rw [hScard]; exact card_goodBases_ge hprime hnodup hE
  have hm : (0 : ℚ) < ℓ.length + 1 := by positivity
  calc (1 : ℚ) / (4 * (ℓ.length + 1)) ≤ ((p : ℚ) - 1) / (ℓ.length + 1) * (1 / (2 * p)) := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hm.le (by linarith : (0 : ℚ) ≤ p - 2)]
    _ ≤ S.card * (1 / p - 1 / 2 ^ B) :=
        mul_le_mul hcardS hx (by positivity) (by positivity)
    _ ≤ eventProb (univ.filter fun v : BitString B ↦ bitsVal v % p ∈ S) :=
        eventProb_bitsVal_mod_mem_ge B p S hS
    _ = eventProb (omegaGood p ℓ.prod ℓ B) := by rw [heq]

/-- `findOmega = none` iff every attempt fails. -/
theorem findOmega_eq_none_iff (p E : ℕ) (ℓ : List ℕ) (t B : ℕ) (w : BitString (t * B)) :
    findOmega p E ℓ t B (List.ofFn w) = none ↔ blockEventCount (omegaGood p E ℓ B) w = 0 := by
  classical
  have hmem : ∀ i : Fin t, blocksEquiv t B w i ∈ omegaGood p E ℓ B ↔
      orderTestNat p E ℓ (powMod (sampleMod p B (List.ofFn w) i) ((p - 1) / E) p) = true := by
    intro i
    simp only [omegaGood, mem_filter, mem_univ, true_and, sampleMod, block, ofFn_blocksEquiv]
  unfold findOmega blockEventCount
  rw [List.findSome?_eq_none_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i _
    rw [hmem]
    have := h i.val (List.mem_range.2 i.isLt)
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false] at this
    simpa using this
  · intro h i hi
    have := h (mem_univ (⟨i, List.mem_range.1 hi⟩ : Fin t))
    rw [hmem] at this
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    simpa using this

theorem eventProb_findOmega_none_le {p : ℕ} [Fact p.Prime] {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime)
    (hnodup : ℓ.Nodup) (hE : ℓ.prod ∣ p - 1) {B : ℕ} (hB : 2 * p ≤ 2 ^ B) (t : ℕ) :
    eventProb (univ.filter fun w : BitString (t * B) ↦ findOmega p ℓ.prod ℓ t B (List.ofFn w) = none) ≤
      (1 - 1 / (4 * (ℓ.length + 1))) ^ t := by
  have heq : (univ.filter fun w : BitString (t * B) ↦ findOmega p ℓ.prod ℓ t B (List.ofFn w) = none) =
      univ.filter fun w ↦ blockEventCount (omegaGood p ℓ.prod ℓ B) w = 0 :=
    filter_congr fun w _ ↦ findOmega_eq_none_iff p ℓ.prod ℓ t B w
  rw [heq, eventProb_blockEventCount_eq_zero]
  apply pow_le_pow_left₀ (by linarith [eventProb_le_one (omegaGood p ℓ.prod ℓ B)])
  linarith [eventProb_omegaGood_ge hprime hnodup hE hB]

/-- With `t ≥ 36 (m + 1)` attempts, failure `≤ 1/10`. -/
theorem eventProb_findOmega_none_le_tenth {p : ℕ} [Fact p.Prime] {ℓ : List ℕ}
    (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) (hE : ℓ.prod ∣ p - 1) {B : ℕ} (hB : 2 * p ≤ 2 ^ B)
    {t : ℕ} (ht : 36 * (ℓ.length + 1) ≤ t) :
    eventProb (univ.filter fun w : BitString (t * B) ↦ findOmega p ℓ.prod ℓ t B (List.ofFn w) = none) ≤
      1 / 10 := by
  refine le_trans (eventProb_findOmega_none_le hprime hnodup hE hB t) ?_
  have hm : (1 : ℚ) ≤ 4 * (ℓ.length + 1) := by
    have : (0 : ℚ) ≤ ℓ.length := by positivity
    linarith
  have ht' : (4 * ((ℓ.length : ℚ) + 1)) * 9 ≤ t := by
    have : ((36 * (ℓ.length + 1) : ℕ) : ℚ) ≤ t := by exact_mod_cast ht
    push_cast at this
    linarith
  have := all_fail_le_of_attempts hm le_rfl (by rw [div_le_one (by positivity)]; exact hm)
    (by norm_num : (0 : ℚ) ≤ 9) ht'
  norm_num at this ⊢
  exact this

/-! ### Compression -/

/-- The compression-failure event on the coefficient block. -/
noncomputable def compressionFail (d : RootData) (ψ : CNF) (B T : ℕ) : Finset (BitString (T * B)) :=
  univ.filter fun w ↦
    d.commonZeros [toPoly d.p (RootData.Hterms d.p (coeffs d.p B (d.m + ψ.length) (List.ofFn w))
      (d.constraintTerms ψ))] ≠ d.commonZeros (d.constraintPolys ψ)

/-! #### Conditioning on a suffix -/

private theorem card_fiber_blockSnd {a b : ℕ} (E : Finset (BitString (a + b))) (v : BitString b) :
    (E.filter fun w ↦ blockSnd a b w = v).card =
      (univ.filter fun u : BitString a ↦ blockAppend a b u v ∈ E).card := by
  apply Finset.card_bij' (fun w _ ↦ blockFst a b w) (fun u _ ↦ blockAppend a b u v)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [← hw.2, blockAppend_fst_snd]
    exact hw.1
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact ⟨hu, blockSnd_append a b u v⟩
  · intro w hw
    simp only [mem_filter] at hw
    rw [← hw.2]
    exact blockAppend_fst_snd a b w
  · intro u _
    exact blockFst_append a b u v

private theorem card_eq_sum_slices_snd {a b : ℕ} (E : Finset (BitString (a + b))) :
    E.card = ∑ v : BitString b, (univ.filter fun u : BitString a ↦ blockAppend a b u v ∈ E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := blockSnd a b) (t := univ) (fun _ _ ↦ mem_univ _)]
  exact Finset.sum_congr rfl fun v _ ↦ card_fiber_blockSnd E v

/-- Upper slice bound, conditioning on the suffix. -/
theorem eventProb_le_of_slices_snd {a b : ℕ} (E : Finset (BitString (a + b))) (q : ℚ)
    (h : ∀ v : BitString b,
      eventProb (univ.filter fun u : BitString a ↦ blockAppend a b u v ∈ E) ≤ q) :
    eventProb E ≤ q := by
  have hpos : (0 : ℚ) < 2 ^ a := by positivity
  have hcard : ∀ v : BitString b,
      ((univ.filter fun u : BitString a ↦ blockAppend a b u v ∈ E).card : ℚ) ≤ q * 2 ^ a := by
    intro v
    have hv := h v
    unfold eventProb at hv
    rwa [div_le_iff₀ hpos] at hv
  unfold eventProb
  rw [div_le_iff₀ (by positivity), card_eq_sum_slices_snd E]
  push_cast
  calc ∑ v : BitString b, ((univ.filter fun u : BitString a ↦ blockAppend a b u v ∈ E).card : ℚ)
      ≤ ∑ _v : BitString b, q * 2 ^ a := Finset.sum_le_sum fun v _ ↦ hcard v
    _ = q * 2 ^ (a + b) := by
      rw [Finset.sum_const, card_univ, card_finArrowBool, pow_add]
      ring

/-- Prefix slice bound for a seed whose length is only propositionally `a + b`. -/
theorem eventProb_le_of_slices_cast {n a b : ℕ} (h : n = a + b) (E : Finset (BitString n)) (q : ℚ)
    (hq : ∀ u : BitString a, eventProb (univ.filter fun v : BitString b ↦
      blockAppend a b u v ∘ Fin.cast h ∈ E) ≤ q) :
    eventProb E ≤ q := by
  subst h
  apply eventProb_le_of_slices E q
  intro u
  simpa using hq u

private theorem ofFn_comp_cast {n m : ℕ} (h : n = m) (f : Fin m → Bool) :
    List.ofFn (f ∘ Fin.cast h) = List.ofFn f := by
  subst h
  simp

/-! #### Changing one block changes one coefficient -/

/-- Blocks disjoint from the window `[|l₁|, |l₁| + |l₂|)` do not depend on `l₂`. -/
private theorem block_append_middle (l₁ l₂ l₂' l₃ : List Bool) (h : l₂.length = l₂'.length)
    {off len : ℕ} (hoff : off + len ≤ l₁.length ∨ l₁.length + l₂.length ≤ off) :
    block (l₁ ++ (l₂ ++ l₃)) off len = block (l₁ ++ (l₂' ++ l₃)) off len := by
  unfold block
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.length_take, List.length_drop, List.length_append] at h₁ h₂
    simp only [List.getElem_take, List.getElem_drop]
    rcases hoff with h1 | h2
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
        List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp only [h]

/-- Changing the `s`-th block only changes the `s`-th coefficient sample. -/
private theorem coeffs_append_middle (p B t s : ℕ) (l₁ l₂ l₂' l₃ : List Bool)
    (h₁ : l₁.length = s * B) (h₂ : l₂.length = B) (h₂' : l₂'.length = B) :
    coeffs p B t (l₁ ++ (l₂ ++ l₃)) = (coeffs p B t (l₁ ++ (l₂' ++ l₃))).set s (decNat l₂ % p) := by
  apply List.ext_getElem
  · simp [length_coeffs]
  · intro i hi _
    rw [length_coeffs] at hi
    simp only [coeffs, List.getElem_map, List.getElem_range, List.getElem_set]
    split_ifs with hsi
    · subst hsi
      simp only [sampleMod, block, List.drop_left' h₁, List.take_left' h₂]
    · simp only [sampleMod]
      rw [block_append_middle l₁ l₂ l₂' l₃ (by omega)]
      rcases Nat.lt_or_gt_of_ne hsi with hlt | hgt
      · right
        have := Nat.mul_le_mul_right B (hlt : s + 1 ≤ i)
        rw [Nat.succ_mul] at this
        omega
      · left
        have := Nat.mul_le_mul_right B (hgt : i + 1 ≤ s)
        rw [Nat.succ_mul] at this
        omega

/-! #### The per-root bound -/

/-- For a root `α` at which some constraint does not vanish, `H(α) = 0` has probability
`≤ 1/p + 2^{-B}`: condition on every block except the one of the distinguished coefficient. -/
private theorem eventProb_eval_Hpoly_eq_zero_le (d : RootData) (ψ : CNF) (B T : ℕ)
    (hT : d.m + ψ.length ≤ T) {α : ZMod d.p}
    (hF : ∃ F ∈ d.constraintPolys ψ, F.eval α ≠ 0) :
    eventProb (univ.filter fun w : BitString (T * B) ↦
      (d.Hpoly ((coeffs d.p B (d.m + ψ.length) (List.ofFn w)).map fun u : ℕ ↦ (u : ZMod d.p))
        (d.constraintPolys ψ)).eval α = 0) ≤ 1 / d.p + 1 / 2 ^ B := by
  classical
  have hFslen : (d.constraintPolys ψ).length = d.m + ψ.length := by
    simp [RootData.constraintPolys]
  obtain ⟨F, hFmem, hFα⟩ := hF
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hFmem
  have hs' : s < d.m + ψ.length := hFslen ▸ hs
  have hp : 0 < d.p := d.hp.pos
  have hTB : T * B = s * B + (B + (T - s - 1) * B) := by
    calc T * B = (s + 1 + (T - s - 1)) * B := by congr 1; omega
      _ = _ := by ring
  apply eventProb_le_of_slices_cast hTB
  intro u
  apply eventProb_le_of_slices_snd
  intro v
  set x₀ : BitString B := fun _ ↦ false with hx₀
  set us₀ : List (ZMod d.p) :=
    (coeffs d.p B (d.m + ψ.length) (List.ofFn u ++ (List.ofFn x₀ ++ List.ofFn v))).map
      (fun u : ℕ ↦ (u : ZMod d.p)) with hus₀
  have hus₀len : us₀.length = (d.constraintPolys ψ).length := by
    simp [hus₀, length_coeffs, hFslen]
  have hkey : ∀ x : BitString B,
      (coeffs d.p B (d.m + ψ.length) (List.ofFn u ++ (List.ofFn x ++ List.ofFn v))).map
        (fun u : ℕ ↦ (u : ZMod d.p)) = us₀.set s ((bitsVal x % d.p : ℕ) : ZMod d.p) := by
    intro x
    rw [coeffs_append_middle d.p B _ s _ _ (List.ofFn x₀) _ (by simp) (by simp) (by simp),
      List.map_set]
    rfl
  obtain ⟨v₀, -, huniq⟩ := d.existsUnique_coeff us₀ hs hus₀len (α := α)
    (by rw [List.get_eq_getElem]; exact hFα)
  refine le_trans (eventProb_filter_mono (Q := fun x : BitString B ↦ bitsVal x % d.p = v₀.val) ?_)
    (eventProb_bitsVal_mod_le B d.p v₀.val hp)
  intro x hx
  simp only [mem_filter, mem_univ, true_and, ofFn_comp_cast, ofFn_blockAppend, hkey] at hx
  have := huniq _ hx
  rw [← this, ZMod.val_natCast, Nat.mod_mod]

/-- **Lemma 17/24, machine sampling version.** -/
theorem eventProb_compressionFail_le (d : RootData) (ψ : CNF) {B : ℕ} (hB : 2 * d.p ≤ 2 ^ B)
    {T : ℕ} (hT : d.m + ψ.length ≤ T) :
    eventProb (compressionFail d ψ B T) ≤ 2 * d.E / d.p := by
  classical
  let Bad : ZMod d.p → Finset (BitString (T * B)) := fun α ↦
    univ.filter fun w ↦
      (d.Hpoly ((coeffs d.p B (d.m + ψ.length) (List.ofFn w)).map fun u : ℕ ↦ (u : ZMod d.p))
        (d.constraintPolys ψ)).eval α = 0
  have hsub : compressionFail d ψ B T ⊆
      (nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ)).biUnion Bad := by
    intro w hw
    simp only [compressionFail, mem_filter, mem_univ, true_and, d.toPoly_Hterms_eq_Hpoly] at hw
    have hss : d.commonZeros (d.constraintPolys ψ) ⊂ d.commonZeros
        [d.Hpoly ((coeffs d.p B (d.m + ψ.length) (List.ofFn w)).map fun u : ℕ ↦ (u : ZMod d.p))
          (d.constraintPolys ψ)] :=
      lt_of_le_of_ne (d.commonZeros_subset_Hpoly _ _) (Ne.symm hw)
    obtain ⟨α, hα, hαZ⟩ := Finset.exists_of_ssubset hss
    rw [mem_biUnion]
    refine ⟨α, ?_, ?_⟩
    · rw [mem_sdiff]
      refine ⟨?_, hαZ⟩
      simp only [RootData.commonZeros, mem_filter] at hα
      exact hα.1
    · simp only [RootData.commonZeros, mem_filter, List.forall_mem_singleton] at hα
      simp only [Bad, mem_filter, mem_univ, true_and]
      exact hα.2
  have hp : 0 < d.p := d.hp.pos
  have hp' : (0 : ℚ) < d.p := by exact_mod_cast hp
  have hB' : (2 : ℚ) * d.p ≤ 2 ^ B := by exact_mod_cast hB
  have hbound : (1 : ℚ) / d.p + 1 / 2 ^ B ≤ 2 / d.p := by
    have h1 : (1 : ℚ) / 2 ^ B ≤ 1 / (2 * d.p) := one_div_le_one_div_of_le (by positivity) hB'
    have h2 : (1 : ℚ) / d.p + 1 / (2 * d.p) ≤ 2 / d.p := by
      rw [div_add_div _ _ hp'.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hcard : ((nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ)).card : ℚ)
      ≤ d.E := by
    have := card_le_card (sdiff_subset (s := nthRootsFinset d.E (1 : ZMod d.p))
      (t := d.commonZeros (d.constraintPolys ψ)))
    rw [d.card_nthRootsFinset_E] at this
    exact_mod_cast this
  calc eventProb (compressionFail d ψ B T)
      ≤ eventProb ((nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ)).biUnion
          Bad) := eventProb_mono hsub
    _ ≤ ∑ α ∈ nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ),
          eventProb (Bad α) := eventProb_biUnion_le _ _
    _ ≤ ∑ _α ∈ nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ),
          ((1 : ℚ) / d.p + 1 / 2 ^ B) := by
        apply Finset.sum_le_sum
        intro α hα
        rw [mem_sdiff] at hα
        have h2 := hα.2
        simp only [RootData.commonZeros, mem_filter, not_and, not_forall] at h2
        obtain ⟨F, hF, hFα⟩ := h2 hα.1
        exact eventProb_eval_Hpoly_eq_zero_le d ψ B T hT ⟨F, hF, hFα⟩
    _ = (nthRootsFinset d.E (1 : ZMod d.p) \ d.commonZeros (d.constraintPolys ψ)).card *
          ((1 : ℚ) / d.p + 1 / 2 ^ B) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ d.E * (2 / d.p) := mul_le_mul hcard hbound (by positivity) (by positivity)
    _ = 2 * d.E / d.p := by ring

end SparseGcd
