import SparseGcd.Machine.TrialUnsat
import SparseGcd.Machine.TrialSat
import SparseGcd.Machine.TrialStr
import SparseDivComplexity.Randomized.RandomTape

/-!
# Error analysis of the reduction (Theorem 18 / Lemma 26)

The two per-trial bounds are proved in `Machine/TrialUnsat.lean` and `Machine/TrialSat.lean`:

* **unsatisfiable `φ`**: `Pr[accept] ≤ 3/2^cnt ≤ 1/(100 r)`
  (`DegreeOracle.eventProb_trialAccept_le_of_unsat`);
* **satisfiable `φ`**: `Pr[accept] ≥ 1/(2A(s))`
  (`DegreeOracle.eventProb_trialAccept_ge_of_sat`).

This file assembles them over the `r = 8 A(s)` independent trial blocks: false acceptance
`≤ r · 1/(100 r) = 1/100 ≤ 1/3` by the union bound (`eventProb_blockEventCount_pos_le`), and
all-reject `≤ (1 - 1/(2A))^{8A} ≤ 1/5` by `all_fail_le_one_fifth`, so the verdict is correct with
probability `≥ 2/3`.

The seed-length polynomial is an explicit polynomial **upper** bound `seedPoly` for `r s · L s`
(an equality is impossible, since `cnt s = Nat.size (400 r s)` is not a polynomial); the verdict
only reads the first `r s · L s` bits of its seed (`verdictData_take`), so padding the tape to
`seedPoly.eval s` bits does not change the acceptance probability.
-/

open Complexity SAT SparseDiv Finset

namespace SparseGcd

/-! ## Polynomial bounds for the parameters of the reduction

Every parameter of the reduction is a polynomial in `s` except `cnt s = Nat.size (400 r s)`,
which is bounded by the polynomial `400 r s`; composing the construction's own polynomials with
the resulting bound for `Nn s` gives polynomial upper bounds for all block lengths. -/

section PolyBounds

open Polynomial

/-- Polynomial form of `Vmax`. -/
noncomputable def VmaxP : Polynomial ℕ := (X + 1) + X + (X + 3) * (X + 1)

@[simp] theorem eval_VmaxP (s : ℕ) : VmaxP.eval s = Vmax s := by
  simp [VmaxP, Vmax]

/-- Polynomial form of `Kmax`. -/
noncomputable def KmaxP : Polynomial ℕ := 3 * X + X + (X + 3) * (4 * (X + 1) + 1)

@[simp] theorem eval_KmaxP (s : ℕ) : KmaxP.eval s = Kmax s := by
  simp [KmaxP, Kmax]

/-- Polynomial form of the number of trials `r`. -/
noncomputable def rP : Polynomial ℕ := 8 * (16 * (X + 4))

@[simp] theorem eval_rP (s : ℕ) : rP.eval s = r s := by
  simp [rP, r, A]

/-- `cnt s = Nat.size (400 r s) ≤ 400 r s`, since `n < 2 ^ n`. -/
theorem cnt_le (s : ℕ) : cnt s ≤ 400 * r s :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Polynomial upper bound for `Nn`. -/
noncomputable def NnP : Polynomial ℕ := VmaxP + 400 * rP + 4

theorem Nn_le (s : ℕ) : Nn s ≤ NnP.eval s := by
  have h := cnt_le s
  simp only [NnP, eval_add, eval_mul, eval_ofNat, eval_VmaxP, eval_rP, Nn]
  omega

/-- Polynomial upper bound for the sample width `C.Bb`. -/
noncomputable def BbP (C : PrimeConstruction) : Polynomial ℕ := C.bitBound.comp NnP + 1

theorem Bb_le (C : PrimeConstruction) (s : ℕ) : C.Bb s ≤ (BbP C).eval s := by
  simp only [BbP, eval_add, eval_one, eval_comp, PrimeConstruction.Bb]
  exact Nat.add_le_add_right (Complexity.polynomial_eval_mono_nat _ (Nn_le s)) 1

/-- Polynomial upper bound for the package seed length `C.Lp`. -/
noncomputable def LpP (C : PrimeConstruction) : Polynomial ℕ := C.seedLen.comp NnP

theorem Lp_le (C : PrimeConstruction) (s : ℕ) : C.Lp s ≤ (LpP C).eval s := by
  simp only [LpP, eval_comp, PrimeConstruction.Lp]
  exact Complexity.polynomial_eval_mono_nat _ (Nn_le s)

/-- Polynomial upper bound for the instance-length bound `C.Zmax`. -/
noncomputable def ZmaxP (C : PrimeConstruction) : Polynomial ℕ :=
  4 * (2 * BbP C + 2 + (2 * (8 * (BbP C + 4)) + 2 +
    (3 * VmaxP + 8 * KmaxP) * (8 * (BbP C + 4)))) + 4

theorem Zmax_le (C : PrimeConstruction) (s : ℕ) : C.Zmax s ≤ (ZmaxP C).eval s := by
  have hb := Bb_le C s
  simp only [ZmaxP, eval_add, eval_mul, eval_ofNat, eval_VmaxP, eval_KmaxP,
    PrimeConstruction.Zmax]
  gcongr

/-- Polynomial upper bound for the oracle seed length `σOr`. -/
noncomputable def sOrP (Or : DegreeOracle) (C : PrimeConstruction) : Polynomial ℕ :=
  Or.σ.comp (400 * rP + ZmaxP C)

theorem sOr_le (Or : DegreeOracle) (C : PrimeConstruction) (s : ℕ) :
    Or.σOr C s ≤ (sOrP Or C).eval s := by
  simp only [sOrP, eval_comp, eval_add, eval_mul, eval_ofNat, eval_rP, DegreeOracle.σOr]
  exact Complexity.polynomial_eval_mono_nat _ (Nat.add_le_add (cnt_le s) (Zmax_le C s))

/-- Polynomial upper bound for the length `Or.L C s` of one trial's seed. -/
noncomputable def LP (Or : DegreeOracle) (C : PrimeConstruction) : Polynomial ℕ :=
  (X + 3) + ((X + 3) * (X + 2) + (4 * LpP C + (36 * (VmaxP + 1) * BbP C +
    ((VmaxP + KmaxP) * BbP C + sOrP Or C))))

theorem KB_le (s : ℕ) : KB s ≤ s + 3 := by
  have h : Nat.size (s + 1 + 2) ≤ s + 3 :=
    Nat.size_le.mpr (by have := Nat.lt_two_pow_self (n := s + 3); omega)
  simpa [KB, kBits] using h

theorem HB_eq (s : ℕ) : HB s = (s + 3) * (s + 2) := by
  simp [HB, hashBits]

theorem L_le (Or : DegreeOracle) (C : PrimeConstruction) (s : ℕ) :
    Or.L C s ≤ (LP Or C).eval s := by
  have hKB := KB_le s
  have hHB := HB_eq s
  have hLp : tp * C.Lp s ≤ 4 * (LpP C).eval s := Nat.mul_le_mul_left 4 (Lp_le C s)
  have hBb := Bb_le C s
  have hta : ta s * C.Bb s ≤ 36 * (Vmax s + 1) * (BbP C).eval s := by
    unfold ta
    exact Nat.mul_le_mul_left _ hBb
  have hTm : Tmax s * C.Bb s ≤ (Vmax s + Kmax s) * (BbP C).eval s := by
    unfold Tmax
    exact Nat.mul_le_mul_left _ hBb
  have hsg := sOr_le Or C s
  rw [DegreeOracle.L_eq_segments]
  simp only [LP, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_VmaxP, eval_KmaxP]
  omega

end PolyBounds

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-- The accepting seeds of the verdict. -/
def verdictAccept (Or : DegreeOracle) (C : PrimeConstruction) (x : List Bool) :
    Finset (BitString (r x.length * Or.L C x.length)) :=
  univ.filter fun w ↦ Or.verdictData C x (List.ofFn w) = true

/-! ### The verdict as a block event -/

/-- If `x` does not decode, the verdict rejects every seed. -/
theorem verdictAccept_eq_empty {x : List Bool} (hd : CNF.decode? x = none) :
    Or.verdictAccept C x = ∅ := by
  unfold verdictAccept
  rw [Finset.filter_eq_empty_iff]
  intro w _
  simp [verdictData, hd]

/-- **The verdict is the block event "some trial accepts".** -/
theorem verdictAccept_eq_blockEvent {x : List Bool} {φ : CNF} (hd : CNF.decode? x = some φ) :
    Or.verdictAccept C x = univ.filter fun w : BitString (r x.length * Or.L C x.length) ↦
      0 < blockEventCount (Or.trialAccept C x.length φ) w := by
  unfold verdictAccept
  refine Finset.filter_congr fun w _ ↦ ?_
  simp only [verdictData, hd, List.any_eq_true, List.mem_range, blockEventCount, Finset.card_pos,
    Finset.filter_nonempty_iff, mem_univ, true_and, trialAccept, mem_filter, ofFn_blocksEquiv,
    block]
  constructor
  · rintro ⟨i, hi, hval⟩
    exact ⟨⟨i, hi⟩, hval⟩
  · rintro ⟨i, hval⟩
    exact ⟨i.1, i.2, hval⟩

/-! ### The two verdict bounds -/

theorem eventProb_verdictAccept_le_of_not_mem {x : List Bool} (hx : x ∉ SAT.language) :
    eventProb (Or.verdictAccept C x) ≤ 1 / 3 := by
  cases hd : CNF.decode? x with
  | none =>
    rw [verdictAccept_eq_empty Or C hd]
    simp only [eventProb, Finset.card_empty, Nat.cast_zero, zero_div]
    norm_num
  | some φ =>
    have hxe : x = CNF.encode φ := CNF.decode?_sound hd
    have hφ : ¬ φ.Satisfiable := fun h ↦ hx ⟨φ, hxe, h⟩
    have hs : (CNF.encode φ).length = x.length := by rw [← hxe]
    have hr : 0 < r x.length := by unfold r A; omega
    have hrQ : (0 : ℚ) < (r x.length : ℚ) := by exact_mod_cast hr
    rw [verdictAccept_eq_blockEvent Or C hd]
    have h1 := eventProb_blockEventCount_pos_le (r x.length) (Or.L C x.length)
      (Or.trialAccept C x.length φ)
    have h2 := eventProb_trialAccept_le_of_unsat Or C hs hφ
    have h3 : (r x.length : ℚ) * eventProb (Or.trialAccept C x.length φ) ≤
        (r x.length : ℚ) * (1 / (100 * r x.length)) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hrQ)
    have h4 : (r x.length : ℚ) * (1 / (100 * r x.length)) = 1 / 100 := by
      field_simp
    linarith

theorem eventProb_verdictAccept_ge_of_mem {x : List Bool} (hx : x ∈ SAT.language) :
    (2 : ℚ) / 3 ≤ eventProb (Or.verdictAccept C x) := by
  obtain ⟨φ, hxe, hφ⟩ := hx
  have hd : CNF.decode? x = some φ := by rw [hxe]; exact CNF.decode?_encode φ
  have hs : (CNF.encode φ).length = x.length := by rw [← hxe]
  rw [verdictAccept_eq_blockEvent Or C hd, eventProb_blockEventCount_pos_eq]
  have hq := eventProb_trialAccept_ge_of_sat Or C hs hφ
  have hq1 := eventProb_le_one (Or.trialAccept C x.length φ)
  have hA : (1 : ℚ) ≤ ((A x.length : ℕ) : ℚ) := by
    have : 1 ≤ A x.length := by unfold A; omega
    exact_mod_cast this
  have hn : 8 * ((A x.length : ℕ) : ℚ) ≤ ((r x.length : ℕ) : ℚ) := by
    have : r x.length = 8 * A x.length := rfl
    rw [this]
    push_cast
    ring_nf
    exact le_refl _
  have hfail := all_fail_le_one_fifth hA hq hq1 hn
  linarith

/-! ### The seed-length polynomial -/

/-- The verdict only reads the first `r |x| · L |x|` bits of its seed. -/
theorem verdictData_take (x seed : List Bool) :
    Or.verdictData C x seed = Or.verdictData C x (seed.take (r x.length * Or.L C x.length)) := by
  simp only [verdictData]
  cases hd : CNF.decode? x with
  | none => rfl
  | some φ =>
    have key : ∀ i, i < r x.length →
        block (seed.take (r x.length * Or.L C x.length)) (i * Or.L C x.length)
            (Or.L C x.length) = block seed (i * Or.L C x.length) (Or.L C x.length) := by
      intro i hi
      refine block_take seed ?_
      calc i * Or.L C x.length + Or.L C x.length = (i + 1) * Or.L C x.length := by ring
        _ ≤ r x.length * Or.L C x.length := Nat.mul_le_mul_right _ hi
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨i, hi, hval⟩
      exact ⟨i, hi, by rw [key i hi]; exact hval⟩
    · rintro ⟨i, hi, hval⟩
      rw [key i hi] at hval
      exact ⟨i, hi, hval⟩

/-- A polynomial **upper bound** for the seed length `r(s) · L(s)` of the verdict: built by
composing `C.seedLen`, `C.bitBound` and `Or.σ` with polynomial bounds for `Nn s` and `cnt s`
(`cnt s = Nat.size (400 r s) ≤ 400 r s`), using `Complexity.polynomial_eval_mono_nat`. -/
noncomputable def seedPoly (Or : DegreeOracle) (C : PrimeConstruction) : Polynomial ℕ :=
  rP * LP Or C

theorem seedPoly_le (s : ℕ) : r s * Or.L C s ≤ (Or.seedPoly C).eval s := by
  simp only [seedPoly, Polynomial.eval_mul, eval_rP]
  exact Nat.mul_le_mul_left _ (L_le Or C s)

/-! ### The random-tape solver -/

open scoped Classical in
/-- **The random-tape solver for SAT.** -/
theorem randomTapeSolves_SAT :
    SparseDiv.RandomTapeSolves (PromiseProblem.ofLanguage SAT.language) (Or.verdictStr C)
      (Or.seedPoly C) := by
  intro x _
  have hnm : r x.length * Or.L C x.length ≤ (Or.seedPoly C).eval x.length := seedPoly_le Or C x.length
  have hgood : goodVerdictSeeds (PromiseProblem.ofLanguage SAT.language) (Or.verdictStr C) x
        ((Or.seedPoly C).eval x.length) =
      univ.filter fun w : BitString ((Or.seedPoly C).eval x.length) ↦
        (Or.verdictData C x (List.ofFn w) = true ↔ x ∈ SAT.language) := by
    unfold goodVerdictSeeds
    refine Finset.filter_congr fun w _ ↦ ?_
    rw [verdictStr_eq]
    simp only [List.cons.injEq, and_true]
    rfl
  rw [hgood, eventProb_filter_take_eq hnm
    (fun l ↦ (Or.verdictData C x l = true ↔ x ∈ SAT.language))
    (fun l ↦ by rw [← verdictData_take])]
  by_cases hx : x ∈ SAT.language
  · refine le_trans (eventProb_verdictAccept_ge_of_mem Or C hx) (le_of_eq ?_)
    unfold verdictAccept
    congr 1
    refine Finset.filter_congr fun w _ ↦ ?_
    simp [hx]
  · have hcompl : (univ.filter fun u : BitString (r x.length * Or.L C x.length) ↦
        (Or.verdictData C x (List.ofFn u) = true ↔ x ∈ SAT.language)) =
        univ.filter fun u : BitString (r x.length * Or.L C x.length) ↦
          ¬ (Or.verdictData C x (List.ofFn u) = true) := by
      refine Finset.filter_congr fun w _ ↦ ?_
      simp [hx]
    rw [hcompl, eventProb_filter_not]
    have := eventProb_verdictAccept_le_of_not_mem Or C hx
    unfold verdictAccept at this
    linarith

/-- **SAT ∈ BPP** given a degree oracle and the prime construction. -/
theorem SAT_mem_BPP (Or : DegreeOracle) (C : PrimeConstruction) : SAT.language ∈ BPP :=
  SparseDiv.mem_BPP_of_randomTape (verdictStr_mem_FP Or C) (randomTapeSolves_SAT Or C)

end DegreeOracle

end SparseGcd
