import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Data.Nat.Size

/-!
# Elementary inequalities used in the error accounting

All probability estimates are carried out over `ℚ`; `e^{-c}` bounds of the paper are replaced by
`(1 - x)^n ≤ 1 / (1 + n x)` (a consequence of Bernoulli's inequality).
-/

namespace SparseGcd

/-- `(1 - x)^n ≤ 1 / (1 + n x)` for `0 ≤ x ≤ 1`. -/
theorem one_sub_pow_le_inv_one_add (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 - x) ^ n ≤ 1 / (1 + n * x) := by
  have hpos : 0 < 1 + (n : ℚ) * x := by positivity
  have h1 : 1 + (n : ℚ) * x ≤ (1 + x) ^ n := one_add_mul_le_pow (by linarith) n
  have h2 : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith) n
  have h3 : (1 - x ^ 2) ^ n ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  rw [le_div_iff₀ hpos]
  calc (1 - x) ^ n * (1 + n * x) ≤ (1 - x) ^ n * (1 + x) ^ n := by gcongr
    _ = (1 - x ^ 2) ^ n := by rw [← mul_pow]; ring_nf
    _ ≤ 1 := h3

/-- With `n ≥ 8 A` trials each succeeding with probability `≥ 1/(2A)`, all fail with probability
at most `1/5`. -/
theorem all_fail_le_one_fifth {A : ℚ} (hA : 1 ≤ A) {q : ℚ} (hq : 1 / (2 * A) ≤ q) (hq1 : q ≤ 1)
    {n : ℕ} (hn : 8 * A ≤ n) : (1 - q) ^ n ≤ 1 / 5 := by
  have hA0 : 0 < A := by linarith
  have hq' : 1 ≤ q * (2 * A) := (div_le_iff₀ (by positivity)).mp hq
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  have h5 : (5 : ℚ) ≤ 1 + n * q := by nlinarith
  calc (1 - q) ^ n ≤ 1 / (1 + n * q) := one_sub_pow_le_inv_one_add q hq0 hq1 n
    _ ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) h5

/-- `t` independent attempts with success `≥ 1/q` (`q ≥ 1`) all fail with probability
`≤ 1/(1 + t/q)`; with `t ≥ q · c` this is `≤ 1/(1+c)`. -/
theorem all_fail_le_of_attempts {q : ℚ} (hq : 1 ≤ q) {s : ℚ} (hs : 1 / q ≤ s) (hs1 : s ≤ 1)
    {t : ℕ} {c : ℚ} (hc : 0 ≤ c) (ht : q * c ≤ t) : (1 - s) ^ t ≤ 1 / (1 + c) := by
  have hq0 : 0 < q := by linarith
  have hs' : 1 ≤ s * q := (div_le_iff₀ hq0).mp hs
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have hc' : 1 + c ≤ 1 + t * s := by nlinarith
  calc (1 - s) ^ t ≤ 1 / (1 + t * s) := one_sub_pow_le_inv_one_add s hs0 hs1 t
    _ ≤ 1 / (1 + c) := one_div_le_one_div_of_le (by linarith) hc'

/-- Natural-number bit length: `Nat.size`. Edge cases `size 0 = 0`, `size 1 = 1`. -/
theorem size_zero' : Nat.size 0 = 0 := Nat.size_zero
theorem size_one' : Nat.size 1 = 1 := Nat.size_one

theorem lt_two_pow_size (n : ℕ) : n < 2 ^ Nat.size n := Nat.lt_size_self n

theorem two_pow_size_le_two_mul {n : ℕ} (hn : 0 < n) : 2 ^ Nat.size n ≤ 2 * n := by
  have hpos : 0 < Nat.size n := Nat.size_pos.mpr hn
  have h : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := by omega

theorem size_le_size_of_le {a b : ℕ} (h : a ≤ b) : Nat.size a ≤ Nat.size b :=
  Nat.size_le_size h

/-- `size (2 n) = size n + 1` for `n > 0`. -/
theorem size_two_mul {n : ℕ} (hn : 0 < n) : Nat.size (2 * n) = Nat.size n + 1 := by
  rw [show 2 * n = n <<< 1 by rw [Nat.shiftLeft_eq]; ring]
  exact Nat.size_shiftLeft (Nat.pos_iff_ne_zero.mp hn) 1

/-- `size (a * b) ≤ size a + size b`. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : Nat.size n ≤ k :=
  Nat.size_le.mpr h

end SparseGcd
