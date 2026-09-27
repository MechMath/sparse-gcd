import Complexitylib.Classes.EventProb
import Complexitylib.Classes.FiniteCounting

/-!
# Majority amplification for per-trial success probability above `1/2`

complexitylib's `binomial_lower_tail_le` bounds the failure probability of a majority vote when each
trial succeeds with probability at least `2/3`. Composing a BPP reduction (error `≤ 1/3`) with an
amplified decider (error `≤ ε`) gives trials that succeed with probability only `≥ 2/3 - ε`, so we
need the same elementary bound for any success probability `p ≥ 1/2`:

`∑_{j ≤ r} C(2r+1, j) p^j (1-p)^{2r+1-j} ≤ (1 - p) · (4 p (1 - p))^r`.

For `p ≥ 3/5` the base `4p(1-p) ≤ 24/25 < 1`, so the majority of `2r + 1` trials errs with
probability at most `(2/5)(24/25)^r`, which is `≤ 1/3` from `r = 5` on.
-/

open Complexity Finset

namespace SparseDiv

/-- **Elementary lower-tail bound for an odd binomial with success probability `p ≥ 1/2`.** -/
theorem binomial_lower_tail_le_of_half_le (r : ℕ) (p : ℚ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    (∑ j ∈ range (r + 1), ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j)) ≤
      (1 - p) * (4 * p * (1 - p)) ^ r := by
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq_le_p : 1 - p ≤ p := by linarith
  calc
    (∑ j ∈ range (r + 1), ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j)) ≤
        ∑ j ∈ range (r + 1), ((2 * r + 1).choose j : ℚ) * (p ^ r * (1 - p) ^ (r + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_range] at hj
      have hjr : j ≤ r := by omega
      have hexp : 2 * r + 1 - j = (r - j) + (r + 1) := by omega
      have hpow : (1 - p) ^ (r - j) ≤ p ^ (r - j) := pow_le_pow_left₀ hq_nonneg hq_le_p _
      calc
        ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j) =
            ((2 * r + 1).choose j : ℚ) * (p ^ j * (1 - p) ^ (r - j)) * (1 - p) ^ (r + 1) := by
          rw [hexp, pow_add]
          ring
        _ ≤ ((2 * r + 1).choose j : ℚ) * (p ^ j * p ^ (r - j)) * (1 - p) ^ (r + 1) := by
          gcongr
        _ = ((2 * r + 1).choose j : ℚ) * (p ^ r * (1 - p) ^ (r + 1)) := by
          rw [← pow_add, Nat.add_sub_of_le hjr]
          ring
    _ = (4 : ℚ) ^ r * (p ^ r * (1 - p) ^ (r + 1)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Nat.cast_sum, Nat.sum_range_choose_halfway]
      norm_cast
    _ = (1 - p) * (4 * p * (1 - p)) ^ r := by
      rw [pow_succ, mul_pow, mul_pow]
      ring

/-- For `p ≥ 3/5`, the lower tail is at most `(2/5)·(24/25)^r`. -/
theorem binomial_lower_tail_le_of_three_fifths_le (r : ℕ) (p : ℚ) (hp : 3 / 5 ≤ p) (hp1 : p ≤ 1) :
    (∑ j ∈ range (r + 1), ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j)) ≤
      (2 / 5) * (24 / 25) ^ r := by
  have hhalf : 1 / 2 ≤ p := by linarith
  have hp_nonneg : 0 ≤ p := by linarith
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq_le : 1 - p ≤ 2 / 5 := by linarith
  have hbase_nonneg : 0 ≤ 4 * p * (1 - p) := by positivity
  have hbase : 4 * p * (1 - p) ≤ 24 / 25 := by
    have h2 : 2 / 5 ≤ p := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr h2)]
  calc
    (∑ j ∈ range (r + 1), ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j)) ≤
        (1 - p) * (4 * p * (1 - p)) ^ r := binomial_lower_tail_le_of_half_le r p hhalf hp1
    _ ≤ (2 / 5) * (24 / 25) ^ r :=
      mul_le_mul hq_le (pow_le_pow_left₀ hbase_nonneg hbase r) (pow_nonneg hbase_nonneg r)
        (by norm_num)

/-- Five extra rounds suffice: `(2/5)(24/25)^5 ≤ 1/3`. -/
theorem two_fifths_mul_pow_five_le : (2 / 5 : ℚ) * (24 / 25) ^ 5 ≤ 1 / 3 := by
  norm_num

/-- **Majority vote with per-trial success `≥ 3/5`.** If a single `T`-bit trial belongs to the event
`E` with probability at least `3/5`, then a strict majority of `2r + 1` independent trials fails
with probability at most `(2/5)(24/25)^r`. -/
theorem eventProb_blockMajority_false_le_of_three_fifths (T r : ℕ) (E : Finset (Fin T → Bool))
    (hE : 3 / 5 ≤ eventProb E) :
    eventProb (univ.filter fun w : Fin ((2 * r + 1) * T) → Bool => blockMajority E w = false) ≤
      (2 / 5) * (24 / 25) ^ r := by
  rw [eventProb_blockMajority_eq_false T r E]
  exact binomial_lower_tail_le_of_three_fifths_le r (eventProb E) hE (eventProb_le_one E)

/-- Eleven trials bring a `3/5` success probability up to `2/3`. -/
theorem eventProb_blockMajority_true_ge_two_thirds (T : ℕ) (E : Finset (Fin T → Bool))
    (hE : 3 / 5 ≤ eventProb E) :
    2 / 3 ≤ eventProb (univ.filter fun w : Fin (11 * T) → Bool => blockMajority E w = true) := by
  rw [eventProb_filter_bool_true]
  have hfail :
      eventProb (univ.filter fun w : Fin (11 * T) → Bool => blockMajority E w = false) ≤
        (2 / 5) * (24 / 25) ^ 5 :=
    eventProb_blockMajority_false_le_of_three_fifths T 5 E hE
  have hbound := two_fifths_mul_pow_five_le
  linarith

/-- Dually, if a single trial lies in `E` with probability at most `2/5`, eleven-trial majority lies
in `E` with probability at most `1/3`. -/
theorem eventProb_blockMajority_true_le_one_third (T : ℕ) (E : Finset (Fin T → Bool))
    (hE : eventProb E ≤ 2 / 5) :
    eventProb (univ.filter fun w : Fin (11 * T) → Bool => blockMajority E w = true) ≤ 1 / 3 := by
  have hcompl : 3 / 5 ≤ eventProb Eᶜ := by
    rw [eventProb_compl]
    linarith
  have htail :
      eventProb (univ.filter fun w : Fin (11 * T) → Bool => blockMajority Eᶜ w = false) ≤
        (2 / 5) * (24 / 25) ^ 5 :=
    eventProb_blockMajority_false_le_of_three_fifths T 5 Eᶜ hcompl
  have hodd : Odd 11 := ⟨5, by norm_num⟩
  have hset :
      univ.filter (fun w : Fin (11 * T) → Bool => blockMajority E w = true) =
        univ.filter (fun w : Fin (11 * T) → Bool => blockMajority Eᶜ w = false) := by
    ext w
    have hflip := blockMajority_compl_of_odd hodd E w
    cases h : blockMajority E w <;> simp_all
  rw [hset]
  exact htail.trans two_fifths_mul_pow_five_le

end SparseDiv
