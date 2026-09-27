import SparseGcd.Machine.SeedSplit

/-!
# One trial on a satisfiable formula (lower bound)

With probability at least `1/A(s)` over segments 1-2 the isolated formula `ψ` is *uniquely*
satisfiable (`eventProb_isolateSeed_unique_padded`). Conditionally on such a prefix the remaining
four segments make the trial accept with probability at least `1/2`, because each of the four
remaining stages fails with small probability:

* the **package** stage fails with probability `≤ 1/2^tp = 1/16`
  (`PrimeConstruction.eventProb_firstPackage_none_le` with `four_le_Nn`, `tp = 4`, and
  `C.Lp s = C.seedLen.eval (Nn s)` by definition);
* the **ω** stage fails with probability `≤ 1/10`
  (`eventProb_findOmega_none_le_tenth`, since `ta s = 36 (Vmax s + 1) ≥ 36 (m + 1)` for
  `m ≤ Vmax s`, and `2 p ≤ 2 ^ Bb s` by `two_mul_p_le_two_pow_Bb`);
* the **compression** fails with probability `≤ 2E/p ≤ 2/2^cnt s`
  (`eventProb_compressionFail_le`, `E_div_p_le_of_le`);
* the **oracle** errs with probability `≤ 1/2^cnt s` (`eventProb_oracle_correct`); on the
  compression-success event `monicGcd d.R (toPoly d.p H) = X - C α` with `α ≠ 0`
  (`RootData.monicGcd_of_success` with `UniqueSat ψ d.m`), so its degree is `1 > 0` and the
  oracle answering correctly means answering `[true]`.

Since `(15/16)(9/10)(1 - 2/2^cnt s)(1 - 1/2^cnt s) ≥ 1/2` (as `2 ^ cnt s > 400 r s ≥ 400`), the
conditional acceptance probability is at least `1/2`, whence
`Pr[accept] ≥ (1/2) · (1/A s) = 1/(2 A s)`.
-/

open Complexity SAT SparseDiv Polynomial Finset

namespace SparseGcd

/-! ## §1 The four stage bounds, as probabilities of "good" seed segments -/

/-- `400 ≤ 2 ^ cnt s`, over `ℚ`. -/
private theorem le_two_pow_cnt_rat (s : ℕ) : (400 : ℚ) ≤ 2 ^ cnt s := by
  have hr : 1 ≤ r s := by unfold r A; omega
  have hlt : 400 * r s < 2 ^ cnt s := lt_two_pow_cnt s
  have h : (400 : ℕ) ≤ 2 ^ cnt s := by omega
  exact_mod_cast h

/-- Both compression/oracle factors are nonnegative. -/
private theorem one_sub_two_div_two_pow_cnt_nonneg (s : ℕ) : 0 ≤ 1 - 2 / (2 : ℚ) ^ cnt s := by
  have h := le_two_pow_cnt_rat s
  have hpos : (0 : ℚ) < 2 ^ cnt s := by positivity
  rw [sub_nonneg, div_le_one hpos]
  linarith

private theorem one_sub_one_div_two_pow_cnt_nonneg (s : ℕ) : 0 ≤ 1 - 1 / (2 : ℚ) ^ cnt s := by
  have h := le_two_pow_cnt_rat s
  have hpos : (0 : ℚ) < 2 ^ cnt s := by positivity
  rw [sub_nonneg, div_le_one hpos]
  linarith

/-- The product of the four stage probabilities is at least `1/2`. -/
private theorem half_le_stage_product (s : ℕ) :
    (1 : ℚ) / 2 ≤
      (1 - 1 / (2 : ℚ) ^ cnt s) * (1 - 2 / (2 : ℚ) ^ cnt s) * (9 / 10) * (15 / 16) := by
  have hpos : (0 : ℚ) < 2 ^ cnt s := by positivity
  have h400 := le_two_pow_cnt_rat s
  have hx0 : (0 : ℚ) < 1 / 2 ^ cnt s := by positivity
  have hx1 : (1 : ℚ) / 2 ^ cnt s ≤ 1 / 400 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have h2 : (2 : ℚ) / 2 ^ cnt s = 2 * (1 / 2 ^ cnt s) := by ring
  rw [h2]
  nlinarith [hx0, hx1, mul_pos hx0 hx0]

/-- Segment 3 (package attempts) succeeds. -/
private def packageGood (C : PrimeConstruction) (s : ℕ) : Finset (BitString (tp * C.Lp s)) :=
  univ.filter fun w ↦ ¬ (C.firstPackage (Nn s) tp (C.Lp s) (List.ofFn w) = none)

/-- The package stage succeeds with probability at least `15/16`. -/
private theorem eventProb_packageGood_ge (C : PrimeConstruction) (s : ℕ) :
    (15 : ℚ) / 16 ≤ eventProb (packageGood C s) := by
  have h : eventProb (univ.filter fun w : BitString (tp * C.Lp s) ↦
      C.firstPackage (Nn s) tp (C.Lp s) (List.ofFn w) = none) ≤ 1 / (2 : ℚ) ^ tp :=
    C.eventProb_firstPackage_none_le (Nn s) tp (four_le_Nn s)
  have h16 : (1 : ℚ) / (2 : ℚ) ^ tp = 1 / 16 := by norm_num [tp]
  rw [h16] at h
  rw [packageGood, eventProb_filter_not]
  linarith

/-- Segment 4 (ω attempts) succeeds. -/
private def omegaStageGood (C : PrimeConstruction) (s p : ℕ) (ℓm : List ℕ) :
    Finset (BitString (ta s * C.Bb s)) :=
  univ.filter fun w ↦ ¬ (findOmega p ℓm.prod ℓm (ta s) (C.Bb s) (List.ofFn w) = none)

/-- The ω stage succeeds with probability at least `9/10`. -/
private theorem eventProb_omegaStageGood_ge (C : PrimeConstruction) {s p : ℕ} [Fact p.Prime]
    {ℓm : List ℕ} (hprime : ∀ q ∈ ℓm, q.Prime) (hnodup : ℓm.Nodup) (hE : ℓm.prod ∣ p - 1)
    (hB : 2 * p ≤ 2 ^ C.Bb s) (hlen : ℓm.length ≤ Vmax s) :
    (9 : ℚ) / 10 ≤ eventProb (omegaStageGood C s p ℓm) := by
  have ht : 36 * (ℓm.length + 1) ≤ ta s := by unfold ta; omega
  have h := eventProb_findOmega_none_le_tenth hprime hnodup hE hB ht
  rw [omegaStageGood, eventProb_filter_not]
  linarith

/-- Segment 5 (coefficients) succeeds with probability at least `1 - 2/2^cnt s`. -/
private theorem eventProb_compressionFail_compl_ge (C : PrimeConstruction) {s : ℕ} (d : RootData)
    (ψ : CNF) (hB : 2 * d.p ≤ 2 ^ C.Bb s) (hT : d.m + ψ.length ≤ Tmax s)
    (hEp : (d.E : ℚ) / d.p ≤ 1 / 2 ^ cnt s) :
    1 - 2 / (2 : ℚ) ^ cnt s ≤ eventProb (compressionFail d ψ (C.Bb s) (Tmax s))ᶜ := by
  rw [eventProb_compl]
  have h := eventProb_compressionFail_le d ψ hB hT
  have h2 : 2 * (d.E : ℚ) / d.p ≤ 2 / 2 ^ cnt s := by
    rw [mul_div_assoc]
    have h3 : (2 : ℚ) / 2 ^ cnt s = 2 * (1 / 2 ^ cnt s) := by ring
    rw [h3]
    linarith
  linarith

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-! ## §2 One trial on a successful package and ω stage -/

/-- On a successful package and ω stage one trial is exactly the oracle's answer. -/
private theorem trialOf_eq_of_stages {s : ℕ} {φ : CNF} (a₁ a₂ a₃ a₄ a₅ a₆ : List Bool)
    {ψ : CNF} {n : ℕ}
    (hiso : isolateSeed φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1))) = (ψ, n))
    {ℓ : List ℕ} {c w : ℕ}
    (hpk : C.firstPackage (Nn s) tp (C.Lp s) a₃ = some (ℓ, c))
    (hfo : findOmega (1 + c * ℓ.prod) (ℓ.take n).prod (ℓ.take n) (ta s) (C.Bb s) a₄ = some w) :
    Or.trialOf C s φ a₁ a₂ a₃ a₄ a₅ a₆ =
      decide (Or.O (pair (unaryN (cnt s)) (pair
        (Or.inst (1 + c * ℓ.prod) (rawRterms (1 + c * ℓ.prod) (ℓ.take n).prod)
          (buildH (1 + c * ℓ.prod) (ℓ.take n).prod (ℓ.take n) w n ψ (C.Bb s) a₅))
        (a₆.take (Or.σOr C s)))) = [true]) := by
  simp only [trialOf, hiso]
  rw [hpk]
  simp only []
  rw [hfo]

/-! ## §3 Segment 6: the oracle answers `[true]` -/

/-- On the compression-success event with a uniquely satisfiable `ψ` the oracle answers `[true]`
with probability at least `1 - 1/2^cnt s`. -/
private theorem eventProb_oracle_true_ge {s : ℕ} (d : RootData) {ψ : CNF} (a₅ : List Bool)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s)
    (hψv : CNF.VarsLt ψ d.m) (hψb : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s)
    (huniq : UniqueSat ψ d.m)
    (hZ : d.commonZeros [toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)] =
      d.commonZeros (d.constraintPolys ψ)) :
    1 - 1 / (2 : ℚ) ^ cnt s ≤ eventProb (univ.filter fun v : BitString (Or.σOr C s) ↦
      Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
        (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)) (List.ofFn v))) = [true]) := by
  have hcard : (solutions ψ d.m).card = 1 := huniq
  have hdeg : 0 <
      (monicGcd d.R (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅))).natDegree := by
    obtain ⟨-, -, h3⟩ := d.monicGcd_of_success hψv hZ
    exact h3.mpr (Finset.card_pos.mp (by rw [hcard]; norm_num))
  refine le_trans (Or.eventProb_oracle_correct C d (C.Bb s) a₅ hp hm hψv hψb hk hcard.le hZ) ?_
  exact eventProb_filter_mono fun v hv ↦ hv.mpr hdeg

/-! ## §4 The two headline bounds -/

open scoped Classical in
/-- **The conditional bound of one trial on a uniquely isolated formula.** Given segments 1-2 on
which the isolation succeeded, the remaining four segments accept with probability at least
`1/2`. -/
theorem eventProb_trialData_ge_of_unique {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (u : BitString (KB s + HB s))
    (hu : UniqueSat (isolateSeed φ ((List.ofFn u).take (kBits (φ.maxVar + 1)))
          (((List.ofFn u).drop (KB s)).take (hashBits (φ.maxVar + 1)))).1
        (isolateSeed φ ((List.ofFn u).take (kBits (φ.maxVar + 1)))
          (((List.ofFn u).drop (KB s)).take (hashBits (φ.maxVar + 1)))).2) :
    (1 : ℚ) / 2 ≤ eventProb (univ.filter fun v : BitString
        (tp * C.Lp s + (ta s * C.Bb s + (Tmax s * C.Bb s + Or.σOr C s))) ↦
      Or.trialData C s φ (List.ofFn u ++ List.ofFn v) = true) := by
  classical
  have hkb := kBits_le_KB hs
  have hhb := hashBits_le_HB hs
  -- §a segments 1-2 as two lists
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : List Bool, a₁ = List.ofFn (blockFst (KB s) (HB s) u) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : List Bool, a₂ = List.ofFn (blockSnd (KB s) (HB s) u) := ⟨_, rfl⟩
  have hlen₁ : a₁.length = KB s := by rw [ha₁]; simp
  have hlen₂ : a₂.length = HB s := by rw [ha₂]; simp
  have hsplit : List.ofFn u = a₁ ++ a₂ := by rw [ha₁, ha₂]; exact ofFn_eq_append_blocks u
  have hA1 : a₁.take (kBits (φ.maxVar + 1)) = (List.ofFn u).take (kBits (φ.maxVar + 1)) := by
    rw [ha₁, ofFn_blockFst, List.take_take, Nat.min_eq_left hkb]
  have hA2 : a₂.take (hashBits (φ.maxVar + 1)) =
      ((List.ofFn u).drop (KB s)).take (hashBits (φ.maxVar + 1)) := by
    rw [ha₂, ofFn_blockSnd]
  -- §b the isolated formula
  obtain ⟨ψ, n, hiso⟩ : ∃ ψ n, isolateSeed φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1))) = (ψ, n) := ⟨_, _, rfl⟩
  have hiso' : isolateSeed φ ((List.ofFn u).take (kBits (φ.maxVar + 1)))
      (((List.ofFn u).drop (KB s)).take (hashBits (φ.maxVar + 1))) = (ψ, n) := by
    rw [← hA1, ← hA2]; exact hiso
  rw [hiso'] at hu
  have huniq : UniqueSat ψ n := hu
  have hψv : CNF.VarsLt ψ n := by
    have h := isolateSeed_varsLt φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rw [hiso] at h; exact h
  have hψb : BoundedClauses ψ := by
    have h := isolateSeed_boundedClauses φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rw [hiso] at h; exact h
  have hkψ : ψ.length ≤ Kmax s := by
    have h := isolateSeed_length_le_Kmax hs (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rw [hiso] at h; exact h
  have hnV : n ≤ Vmax s := by
    have h := isolateSeed_snd_le_Vmax hs (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rw [hiso] at h; exact h
  have hc1 := one_sub_one_div_two_pow_cnt_nonneg s
  -- §c segment 3
  refine le_trans ?_ (eventProb_filter_ge_of_split (a := tp * C.Lp s)
    (b := ta s * C.Bb s + (Tmax s * C.Bb s + Or.σOr C s)) rfl
    (fun l ↦ Or.trialData C s φ (List.ofFn u ++ l) = true) (packageGood C s)
    ((1 - 1 / (2 : ℚ) ^ cnt s) * (1 - 2 / (2 : ℚ) ^ cnt s) * (9 / 10)) ?_)
  · exact le_trans (half_le_stage_product s)
      (mul_le_mul_of_nonneg_left (eventProb_packageGood_ge C s)
        (mul_nonneg (mul_nonneg hc1 (one_sub_two_div_two_pow_cnt_nonneg s)) (by norm_num)))
  intro a₃ ha₃
  simp only [packageGood, mem_filter, mem_univ, true_and] at ha₃
  obtain ⟨⟨ℓ, c⟩, hpk⟩ := Option.ne_none_iff_exists'.mp ha₃
  obtain ⟨hv, hbit⟩ := C.firstPackage_sound hpk
  have : Fact (1 + c * ℓ.prod).Prime := ⟨hv.2.2.2.2⟩
  have hnN : n ≤ Nn s := by unfold Nn; omega
  have hprime : ∀ q ∈ ℓ.take n, q.Prime := fun q hq ↦ hv.2.2.1 q (List.mem_of_mem_take hq)
  have hnodup : (ℓ.take n).Nodup := hv.2.1.sublist (List.take_sublist _ _)
  have hdvd : (ℓ.take n).prod ∣ 1 + c * ℓ.prod - 1 := hv.toPackage.E_dvd_p_sub_one n
  have hBb : 2 * (1 + c * ℓ.prod) ≤ 2 ^ C.Bb s := two_mul_p_le_two_pow_Bb C hbit
  have htakelen : (ℓ.take n).length ≤ Vmax s := by rw [List.length_take]; omega
  -- §d segment 4
  refine le_trans ?_ (eventProb_filter_ge_of_split (a := ta s * C.Bb s)
    (b := Tmax s * C.Bb s + Or.σOr C s) rfl
    (fun l ↦ Or.trialData C s φ (List.ofFn u ++ (List.ofFn a₃ ++ l)) = true)
    (omegaStageGood C s (1 + c * ℓ.prod) (ℓ.take n))
    ((1 - 1 / (2 : ℚ) ^ cnt s) * (1 - 2 / (2 : ℚ) ^ cnt s)) ?_)
  · exact mul_le_mul_of_nonneg_left
      (eventProb_omegaStageGood_ge C hprime hnodup hdvd hBb htakelen)
      (mul_nonneg hc1 (one_sub_two_div_two_pow_cnt_nonneg s))
  intro a₄ ha₄
  simp only [omegaStageGood, mem_filter, mem_univ, true_and] at ha₄
  obtain ⟨w, hfo⟩ := Option.ne_none_iff_exists'.mp ha₄
  obtain ⟨d, hdp, hdE, hdℓ, hdw, hdm⟩ :
      ∃ d : RootData, d.p = 1 + c * ℓ.prod ∧ d.E = (ℓ.take n).prod ∧ d.ℓ = ℓ.take n ∧
        d.w = w ∧ d.m = n :=
    ⟨stageData hv n hfo, rfl, rfl, rfl, rfl, stageData_m hv n hnN hfo⟩
  have hdpB : 2 * d.p ≤ 2 ^ C.Bb s := by rw [hdp]; exact hBb
  have hdpbit : Nat.size d.p ≤ C.bitBound.eval (Nn s) := by rw [hdp]; exact hbit
  have hdmV : d.m ≤ Vmax s := by rw [hdm]; exact hnV
  have hdT : d.m + ψ.length ≤ Tmax s := by rw [hdm]; unfold Tmax; omega
  have hdEp : (d.E : ℚ) / d.p ≤ 1 / 2 ^ cnt s := by
    have h := E_div_p_le_of_le hv (m := n) (s := s) rfl hnV
    rw [hdE, hdp, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    exact h
  -- §e segment 5
  refine le_trans ?_ (eventProb_filter_ge_of_split (a := Tmax s * C.Bb s) (b := Or.σOr C s) rfl
    (fun l ↦ Or.trialData C s φ (List.ofFn u ++ (List.ofFn a₃ ++ (List.ofFn a₄ ++ l))) = true)
    (compressionFail d ψ (C.Bb s) (Tmax s))ᶜ (1 - 1 / (2 : ℚ) ^ cnt s) ?_)
  · exact mul_le_mul_of_nonneg_left
      (eventProb_compressionFail_compl_ge C d ψ hdpB hdT hdEp) hc1
  intro a₅ ha₅
  rw [Finset.mem_compl] at ha₅
  have hcf : d.commonZeros [toPoly d.p (RootData.Hterms d.p
      (coeffs d.p (C.Bb s) (d.m + ψ.length) (List.ofFn a₅)) (d.constraintTerms ψ))] =
      d.commonZeros (d.constraintPolys ψ) := by
    by_contra hne
    exact ha₅ (by simp only [compressionFail, mem_filter, mem_univ, true_and]; exact hne)
  have hZ : d.commonZeros [toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) (List.ofFn a₅))] =
      d.commonZeros (d.constraintPolys ψ) := by
    rw [toPoly_buildH]; exact hcf
  -- §f segment 6
  have hor := Or.eventProb_oracle_true_ge C d (List.ofFn a₅) hdpbit hdmV
    (by rw [hdm]; exact hψv) hψb hkψ (by rw [hdm]; exact huniq) hZ
  rw [hdp, hdE, hdℓ, hdw, hdm] at hor
  refine le_trans hor (eventProb_filter_mono fun v hv2 ↦ ?_)
  rw [hsplit, List.append_assoc,
    trialData_eq_trialOf' Or C hs a₁ a₂ (List.ofFn a₃) (List.ofFn a₄) (List.ofFn a₅) (List.ofFn v)
      hlen₁ hlen₂ (by simp) (by simp) (by simp),
    trialOf_eq_of_stages Or C a₁ a₂ (List.ofFn a₃) (List.ofFn a₄) (List.ofFn a₅) (List.ofFn v)
      hiso hpk hfo]
  have htv : (List.ofFn v).take (Or.σOr C s) = List.ofFn v :=
    List.take_of_length_le (by simp)
  rw [htv]
  simp only [decide_eq_true_eq]
  exact hv2

open scoped Classical in
/-- **The trial-level lower bound on a satisfiable formula.** -/
theorem eventProb_trialAccept_ge_of_sat {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (hφ : φ.Satisfiable) :
    (1 : ℚ) / (2 * A s) ≤ eventProb (Or.trialAccept C s φ) := by
  have hG := eventProb_isolateSeed_unique_padded hs hφ
  have hmain := eventProb_trialAccept_ge_of_prefix Or C (L_eq_prefix_segments Or C s)
    (univ.filter fun w : BitString (KB s + HB s) ↦
      UniqueSat (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
            (((List.ofFn w).drop (KB s)).take (hashBits (φ.maxVar + 1)))).1
          (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
            (((List.ofFn w).drop (KB s)).take (hashBits (φ.maxVar + 1)))).2)
    ((1 : ℚ) / 2)
    (fun u hu ↦ eventProb_trialData_ge_of_unique Or C hs u (by simpa using hu))
  refine le_trans ?_ hmain
  have hA : (0 : ℚ) < A s := by
    have : 0 < A s := by unfold A; omega
    exact_mod_cast this
  have hstep : (1 : ℚ) / 2 * (1 / A s) ≤ 1 / 2 * eventProb _ :=
    mul_le_mul_of_nonneg_left hG (by norm_num)
  refine le_trans (le_of_eq ?_) hstep
  field_simp

end DegreeOracle

end SparseGcd
