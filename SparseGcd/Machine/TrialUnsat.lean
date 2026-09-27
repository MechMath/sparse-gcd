import SparseGcd.Machine.SeedSplit

/-!
# One trial on an unsatisfiable formula (upper bound)

If `φ` is unsatisfiable then every isolated formula `ψ` is unsatisfiable, so `solutions ψ m = ∅`.
A trial can accept only if the package stage returns a valid package and the ω stage returns a
residue passing the order test (otherwise `trialData` is `false`); conditionally on those two
segments, either

* the **compression** fails, i.e. `Z(R, H) ≠ Z(R, F)`, which has probability
  `≤ 2E/p ≤ 2/2^cnt s` over segment 5 (`eventProb_compressionFail_le` together with
  `E_div_p_le_of_le` and `two_mul_p_le_two_pow_Bb`), or
* the compression succeeds, in which case `monicGcd d.R (toPoly d.p H) = 1`
  (`RootData.monicGcd_of_success` with `solutions ψ d.m = ∅`), so its degree is `0` and the oracle
  must err — probability `≤ 1/2^cnt s` over segment 6 (`eventProb_oracle_correct`).

Hence `Pr[accept] ≤ 3/2^cnt s ≤ 1/(100 r s)` by `lt_two_pow_cnt`.
-/

open Complexity SAT SparseDiv Polynomial Finset

namespace SparseGcd

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-! ### The oracle stage on an unsatisfiable formula -/

/-- On the compression-success event of an *unsatisfiable* `ψ` the gcd is `1`, so an accepting
oracle answer is an error: it has probability at most `2^{-cnt s}` over segment 6. -/
theorem eventProb_oracle_accept_le_of_unsat {s : ℕ} (d : RootData) {ψ : CNF} (a₅ : List Bool)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s)
    (hψv : CNF.VarsLt ψ d.m) (hψb : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s)
    (hsol : solutions ψ d.m = ∅)
    (hZ : d.commonZeros [toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)] =
      d.commonZeros (d.constraintPolys ψ)) :
    eventProb (univ.filter fun v : BitString (Or.σOr C s) ↦
      Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
        (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)) (List.ofFn v))) = [true]) ≤
      1 / (2 : ℚ) ^ cnt s := by
  have hcard : (solutions ψ d.m).card ≤ 1 := by rw [hsol]; simp
  have hgcd : monicGcd d.R (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)) = 1 :=
    (d.monicGcd_of_success hψv hZ).1 hsol
  have hdeg : ¬ 0 <
      (monicGcd d.R (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅))).natDegree := by
    rw [hgcd]
    simp
  have hcor := eventProb_oracle_correct Or C d (C.Bb s) a₅ hp hm hψv hψb hk hcard hZ
  have h1 : eventProb (univ.filter fun v : BitString (Or.σOr C s) ↦
        Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
          (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)) (List.ofFn v))) = [true]) ≤
      eventProb (univ.filter fun v : BitString (Or.σOr C s) ↦
        ¬ (Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
            (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅)) (List.ofFn v))) = [true] ↔
          0 < (monicGcd d.R
            (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) a₅))).natDegree)) :=
    eventProb_filter_mono fun _ hv hiff ↦ hdeg (hiff.1 hv)
  rw [eventProb_filter_not] at h1
  linarith

/-! ### Segments 5 and 6 together -/

/-- **The conditional bound over the coefficient and oracle segments.** On an unsatisfiable `ψ`,
either the compression fails (probability `≤ 2 E/p ≤ 2/2^cnt s`) or the oracle errs
(probability `≤ 1/2^cnt s`). -/
theorem eventProb_stages56_le_of_unsat {s : ℕ} (d : RootData) {ψ : CNF} {m : ℕ} (hdm : d.m = m)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s)
    (hψv : CNF.VarsLt ψ d.m) (hψb : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s)
    (hsol : solutions ψ d.m = ∅) (hEp : (d.E : ℚ) / d.p ≤ 1 / 2 ^ cnt s)
    (hB : 2 * d.p ≤ 2 ^ C.Bb s) (hT : d.m + ψ.length ≤ Tmax s) :
    eventProb (univ.filter fun v : BitString (Tmax s * C.Bb s + Or.σOr C s) ↦
      Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
        (buildH d.p d.E d.ℓ d.w m ψ (C.Bb s)
          (List.ofFn (blockFst (Tmax s * C.Bb s) (Or.σOr C s) v))))
        (List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) v)))) = [true]) ≤
      3 / (2 : ℚ) ^ cnt s := by
  classical
  subst hdm
  have hsplit : (3 : ℚ) / 2 ^ cnt s = 2 / 2 ^ cnt s + 1 / 2 ^ cnt s := by ring
  rw [hsplit]
  refine eventProb_le_of_good_prefix _ (compressionFail d ψ (C.Bb s) (Tmax s))ᶜ
    (2 / 2 ^ cnt s) (1 / 2 ^ cnt s) (by positivity) ?_ ?_
  · rw [compl_compl]
    refine le_trans (eventProb_compressionFail_le d ψ hB hT) ?_
    calc 2 * (d.E : ℚ) / d.p = 2 * ((d.E : ℚ) / d.p) := by ring
      _ ≤ 2 * (1 / 2 ^ cnt s) := by linarith
      _ = 2 / 2 ^ cnt s := by ring
  · intro u hu
    rw [Finset.mem_compl] at hu
    simp only [compressionFail, mem_filter, mem_univ, true_and, not_not] at hu
    have hZ : d.commonZeros [toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ (C.Bb s) (List.ofFn u))] =
        d.commonZeros (d.constraintPolys ψ) := by
      rw [toPoly_buildH]
      exact hu
    refine le_trans (le_of_eq ?_)
      (eventProb_oracle_accept_le_of_unsat Or C d (List.ofFn u) hp hm hψv hψb hk hsol hZ)
    congr 1
    refine Finset.filter_congr fun v _ ↦ ?_
    simp only [mem_filter, mem_univ, true_and, blockFst_append, blockSnd_append]

/-! ### The conditional per-trial bound -/

set_option linter.unusedVariables false in
/-- **The conditional bound of one trial on an unsatisfiable formula.** Whatever the first four
segments are, the last two make the trial accept with probability at most `3/2^cnt s`. -/
theorem eventProb_trialOf_le_of_unsat {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (hφ : ¬ φ.Satisfiable) (a₁ a₂ a₃ a₄ : List Bool) (h₁ : a₁.length = KB s)
    (h₂ : a₂.length = HB s) (h₃ : a₃.length = tp * C.Lp s) (h₄ : a₄.length = ta s * C.Bb s) :
    eventProb (univ.filter fun v : BitString (Tmax s * C.Bb s + Or.σOr C s) ↦
      Or.trialOf C s φ a₁ a₂ a₃ a₄
        (List.ofFn (blockFst (Tmax s * C.Bb s) (Or.σOr C s) v))
        (List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) v)) = true) ≤ 3 / 2 ^ cnt s := by
  classical
  obtain ⟨ψ, m, hψm⟩ : ∃ ψ m, isolateSeed φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1))) = (ψ, m) := ⟨_, _, rfl⟩
  have hvars : CNF.VarsLt ψ m := by
    have := isolateSeed_varsLt φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rwa [hψm] at this
  have hbound : BoundedClauses ψ := by
    have := isolateSeed_boundedClauses φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rwa [hψm] at this
  have hmV : m ≤ Vmax s := by
    have := isolateSeed_snd_le_Vmax hs (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rwa [hψm] at this
  have hkK : ψ.length ≤ Kmax s := by
    have := isolateSeed_length_le_Kmax hs (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1)))
    rwa [hψm] at this
  have hsolm : solutions ψ m = ∅ := by
    refine (not_satisfiable_iff_solutions_eq_empty hvars).1 ?_
    have := isolateSeed_unsat φ (a₁.take (kBits (φ.maxVar + 1)))
      (a₂.take (hashBits (φ.maxVar + 1))) hφ
    rwa [hψm] at this
  rcases hpk : C.firstPackage (Nn s) tp (C.Lp s) a₃ with _ | ⟨ℓ, c⟩
  · simp [DegreeOracle.trialOf, hpk]
    positivity
  · obtain ⟨hv, hbit⟩ := C.firstPackage_sound hpk
    rcases hom : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) (ta s) (C.Bb s) a₄ with
      _ | w
    · simp [DegreeOracle.trialOf, hpk, hψm, hom]
      positivity
    · simp only [DegreeOracle.trialOf, hpk, hψm, hom]
      have htake : ∀ x : BitString (Tmax s * C.Bb s + Or.σOr C s),
          List.take (Or.σOr C s) (List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) x)) =
            List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) x) :=
        fun x ↦ List.take_of_length_le (by simp)
      simp only [decide_eq_true_eq, htake]
      have hdm : (stageData hv m hom).m = m :=
        stageData_m hv m (by unfold Nn; omega) hom
      have hEp : (((stageData hv m hom).E : ℕ) : ℚ) / (((stageData hv m hom).p : ℕ) : ℚ) ≤
          1 / 2 ^ cnt s := by
        have h := E_div_p_le_of_le hv (rfl : Nn s = Nn s) hmV
        have e : (((stageData hv m hom).p : ℕ) : ℚ) = 1 + (c : ℚ) * (ℓ.prod : ℚ) := by
          show ((1 + c * ℓ.prod : ℕ) : ℚ) = 1 + (c : ℚ) * (ℓ.prod : ℚ)
          push_cast
          ring
        have e2 : (((stageData hv m hom).E : ℕ) : ℚ) = (((ℓ.take m).prod : ℕ) : ℚ) := rfl
        rw [e, e2]
        exact h
      refine eventProb_stages56_le_of_unsat Or C (stageData hv m hom) hdm hbit ?_ ?_ hbound hkK ?_
        hEp (two_mul_p_le_two_pow_Bb C hbit) ?_
      · rw [hdm]; exact hmV
      · rw [hdm]; exact hvars
      · rw [hdm]; exact hsolm
      · rw [hdm]; unfold Tmax; omega

/-! ### The per-trial bound -/

/-- `3/2^cnt s ≤ 1/(100 r s)`, from `400 r s < 2 ^ cnt s`. -/
theorem three_div_two_pow_cnt_le (s : ℕ) : 3 / (2 : ℚ) ^ cnt s ≤ 1 / (100 * r s) := by
  have hr : 0 < r s := by
    unfold r A
    omega
  have hlt : 400 * r s < 2 ^ cnt s := lt_two_pow_cnt s
  have hr' : (0 : ℚ) < r s := by exact_mod_cast hr
  have hpow : (0 : ℚ) < 2 ^ cnt s := by positivity
  have hkey : (300 : ℚ) * r s ≤ 2 ^ cnt s := by
    have : ((400 * r s : ℕ) : ℚ) ≤ ((2 ^ cnt s : ℕ) : ℚ) := by exact_mod_cast hlt.le
    push_cast at this
    linarith
  rw [div_le_div_iff₀ hpow (by positivity)]
  linarith

/-- **The trial-level upper bound on an unsatisfiable formula.** -/
theorem eventProb_trialAccept_le_of_unsat {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (hφ : ¬ φ.Satisfiable) :
    eventProb (Or.trialAccept C s φ) ≤ 1 / (100 * r s) :=
  le_trans
    (eventProb_trialAccept_le_of_stages Or C hs (3 / 2 ^ cnt s)
      fun a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ ↦
        eventProb_trialOf_le_of_unsat Or C hs hφ a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄)
    (three_div_two_pow_cnt_le s)

end DegreeOracle

end SparseGcd
